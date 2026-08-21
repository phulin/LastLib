/**
 * goal-loop — an OpenCode V2 plugin implementing a self-terminating agent loop.
 *
 * `/goal <text>` registers a persistent goal for the current session. From then
 * on, the agent must end EVERY round by calling the `goal_certify` tool:
 *   - `complete: true`  -> completion sentinel; the loop closes, or
 *   - `complete: false` -> progress report; the loop continues.
 *
 * If a round ends without the sentinel (the agent stopped early, rambled, or
 * tried to dodge), the plugin sees the missing certification on `session.idle`
 * and deterministically injects a synthetic continuation message. The loop is
 * bounded by `options.maxRounds`.
 *
 * The active goal is shown in the session title. `/goal pause` (or a user
 * interrupt) preserves the goal without driving further rounds; `/goal resume`
 * restores the active loop.
 *
 * Install (project-local, auto-discovered):
 *   .opencode/plugins/goal-loop.ts          <- this file
 *   .opencode/package.json                  <- {"dependencies":{"@opencode-ai/plugin":"beta"}}
 *   cd .opencode && npm install
 *
 * Or register explicitly with options:
 *   { "plugins": [{ "package": "./plugins/goal-loop.ts", "options": { "maxRounds": 25 } }] }
 */
import { Plugin } from "@opencode-ai/plugin";

const CERT_TOOL = "goal_certify";

/** Per-session loop state. In-memory by design: loops die with the server. */
type GoalState = {
  goal: string;
  /** Rounds the loop has driven so far. */
  round: number;
  /** Set by goal_certify during the current round; reset when a new round starts. */
  certified: boolean;
  /** Terminal: sentinel accepted, aborted, or cancelled. */
  closed: boolean;
  /** Paused (user interrupt or /goal pause): driver holds off until /goal resume. */
  paused: boolean;
  /** True while we are driving the session after injecting a continuation. */
  driving: boolean;
  /** Original session title, restored when the loop closes. */
  titleBackup?: string;
};

const goals = new Map<string, GoalState>();

const GOAL_MARK = "\u{1F3AF} "; // 🎯
const PAUSED_MARK = "\u{23F8}\u{FE0F} "; // ⏸️

const titleFor = (goal: string): string =>
  GOAL_MARK + (goal.length > 60 ? `${goal.slice(0, 57)}...` : goal);

const pausedTitleFor = (goal: string): string => PAUSED_MARK + titleFor(goal);

export default Plugin.define({
  id: "lastlib.goal-loop",

  setup: (ctx) => {
    const rawRounds = (ctx.options as { maxRounds?: unknown } | undefined)?.maxRounds;
    const maxRounds =
      typeof rawRounds === "number" && Number.isFinite(rawRounds) && rawRounds > 0
        ? Math.floor(rawRounds)
        : 50;

    /** Rename without allowing a cosmetic failure to break the loop. */
    const rename = async (sid: string, title: string) => {
      try {
        await ctx.session.rename({ sessionID: sid, title });
      } catch (error) {
        console.error("[goal-loop] session rename failed:", error);
      }
    };

    /** Close a loop terminally and give the session its title back. */
    const closeLoop = async (sid: string, state: GoalState) => {
      if (state.closed) return;
      state.closed = true;
      state.paused = false;
      if (state.titleBackup !== undefined) {
        await rename(sid, state.titleBackup);
      }
    };

    const protocolPrompt = (state: GoalState): string =>
      [
        "=== GOAL LOOP PROTOCOL (ACTIVE) ===",
        `Persistent goal: ${state.goal}`,
        "",
        "You are operating inside a goal loop. Rules:",
        "1. Spend each round doing concrete work toward the goal.",
        `2. At the END of every single reply you MUST call the \`${CERT_TOOL}\` tool exactly once:`,
        "   - complete: true ONLY when the goal is fully achieved and verifiably so.",
        "   - complete: false otherwise, with a summary of progress and the next step.",
        `3. Ending a round without calling \`${CERT_TOOL}\` is a protocol violation:`,
        "   the harness will deterministically continue you until you certify.",
        "4. Do not claim completion unless the goal text is satisfied. When in doubt,",
        "   certify complete: false.",
        "===================================",
      ].join("\n");

    //
    // /goal command — register a goal, or pause/resume the current one.
    //
    void ctx.command.transform((commands) => {
      commands.update("goal", (command) => {
        command.description =
          "Set, pause, or resume a persistent goal with end-of-round certification";
        command.template = [
          "Interpret the following `/goal` argument:",
          "",
          "$ARGUMENTS",
          "",
          "- If it is exactly `pause`, call `goal_pause`.",
          "- If it is exactly `resume`, call `goal_resume`, then immediately continue the saved goal.",
          "- Otherwise call `goal_set` with the argument quoted verbatim, then immediately begin working toward it.",
          `After setting or resuming a goal, every round must end with a \`${CERT_TOOL}\` call.`,
          "A pause command ends without certification because the loop is then paused.",
        ].join("\n");
      });
    });

    //
    // Tools. codemode:false exposes them directly to the provider — the
    // sentinel must be callable as a plain tool call, not buried in Code Mode.
    //
    void ctx.tool.transform((tools) => {
      tools.add({
        name: "goal_set",
        description:
          "Register (or replace) this session's persistent goal and arm the certification loop.",
        options: { codemode: false },
        input: {
          type: "object",
          properties: {
            goal: {
              type: "string",
              description: "The goal, stated precisely enough that completion is decidable.",
            },
          },
          required: ["goal"],
          additionalProperties: false,
        },
        output: {
          type: "object",
          properties: { status: { type: "string" } },
          required: ["status"],
          additionalProperties: false,
        },
        execute: async (input: unknown, toolCtx) => {
          const goal = (input as { goal?: unknown } | null)?.goal;
          if (typeof goal !== "string" || goal.trim().length === 0) {
            throw new Error("goal_set requires a non-empty string `goal`.");
          }
          const previous = goals.get(toolCtx.sessionID);
          let titleBackup = previous && !previous.closed ? previous.titleBackup : undefined;
          if (titleBackup === undefined) {
            try {
              titleBackup = (await ctx.session.get({ sessionID: toolCtx.sessionID })).title;
            } catch (error) {
              console.error("[goal-loop] failed to capture session title:", error);
            }
          }
          goals.set(toolCtx.sessionID, {
            goal,
            round: 0,
            certified: false,
            closed: false,
            paused: false,
            driving: false,
            titleBackup,
          });
          await rename(toolCtx.sessionID, titleFor(goal));
          const replaced = previous && !previous.closed ? " (previous goal discarded)" : "";
          return {
            output: { status: "registered" },
            content: `Goal armed${replaced}. Every round must end with a \`${CERT_TOOL}\` call.`,
          };
        },
      });

      tools.add({
        name: "goal_pause",
        description:
          "Pause the current goal loop. Use for `/goal pause`; the saved goal can later be resumed.",
        options: { codemode: false },
        input: {
          type: "object",
          properties: {},
          additionalProperties: false,
        },
        output: {
          type: "object",
          properties: { status: { type: "string" } },
          required: ["status"],
          additionalProperties: false,
        },
        execute: async (_input: unknown, toolCtx) => {
          const state = goals.get(toolCtx.sessionID);
          if (!state || state.closed) {
            return {
              output: { status: "no-active-goal" },
              content: "No active goal loop to pause.",
            };
          }
          state.paused = true;
          state.certified = false;
          await rename(toolCtx.sessionID, pausedTitleFor(state.goal));
          return {
            output: { status: "paused" },
            content: `Goal loop paused. Run \`/goal resume\` to continue: ${state.goal}`,
          };
        },
      });

      tools.add({
        name: "goal_resume",
        description:
          "Resume the saved goal loop. Use for `/goal resume`, then continue working toward the goal.",
        options: { codemode: false },
        input: {
          type: "object",
          properties: {},
          additionalProperties: false,
        },
        output: {
          type: "object",
          properties: {
            status: { type: "string" },
            goal: { type: "string" },
          },
          required: ["status", "goal"],
          additionalProperties: false,
        },
        execute: async (_input: unknown, toolCtx) => {
          const state = goals.get(toolCtx.sessionID);
          if (!state || state.closed) {
            return {
              output: { status: "no-paused-goal", goal: "" },
              content: "No paused goal loop to resume. Use `/goal <text>` to set one.",
            };
          }
          if (!state.paused) {
            return {
              output: { status: "already-active", goal: state.goal },
              content: `Goal loop is already active: ${state.goal}`,
            };
          }
          state.paused = false;
          state.certified = false;
          await rename(toolCtx.sessionID, titleFor(state.goal));
          return {
            output: { status: "resumed", goal: state.goal },
            content: `Goal loop resumed. Continue working now: ${state.goal}`,
          };
        },
      });

      tools.add({
        name: CERT_TOOL,
        description:
          "MANDATORY end-of-round certification. Call exactly once at the end of every reply while a goal is active. complete:true closes the loop; complete:false continues it.",
        options: { codemode: false },
        input: {
          type: "object",
          properties: {
            complete: {
              type: "boolean",
              description: "true only if the goal is fully and verifiably achieved.",
            },
            summary: {
              type: "string",
              description: "What was accomplished this round, and (if incomplete) the next step.",
            },
          },
          required: ["complete", "summary"],
          additionalProperties: false,
        },
        output: {
          type: "object",
          properties: {
            accepted: { type: "boolean" },
            loop: { type: "string", enum: ["closed", "open"] },
          },
          required: ["accepted", "loop"],
          additionalProperties: false,
        },
        execute: async (input: unknown, toolCtx) => {
          const args = (input ?? {}) as { complete?: unknown; summary?: unknown };
          const state = goals.get(toolCtx.sessionID);
          if (!state || state.closed) {
            return {
              output: { accepted: false, loop: "closed" as const },
              content: "No active goal loop; certification ignored.",
            };
          }
          if (state.paused) {
            return {
              output: { accepted: false, loop: "open" as const },
              content: "Goal loop is paused; run `/goal resume` before certifying.",
            };
          }
          if (typeof args.complete !== "boolean") {
            throw new Error("goal_certify requires a boolean `complete`.");
          }
          const summary =
            typeof args.summary === "string" && args.summary.trim().length > 0
              ? args.summary.trim()
              : "(no summary provided)";
          state.certified = true;
          if (args.complete) await closeLoop(toolCtx.sessionID, state);
          return {
            output: {
              accepted: true,
              loop: (args.complete ? "closed" : "open") as "closed" | "open",
            },
            content: args.complete
              ? `Completion sentinel accepted. Loop closed.\n${summary}`
              : `Certification recorded (incomplete). Loop continues.\n${summary}`,
          };
        },
      });
    });

    //
    // Inject the protocol into the system prompt on every dispatch while a
    // goal is active, so the contract survives long turns and compaction.
    //
    void ctx.session.hook("context", (event) => {
      const state = goals.get(event.sessionID);
      if (!state || state.closed || state.paused) return;
      event.system.push({ type: "text", text: protocolPrompt(state) });
    });

    //
    // The deterministic continuation driver: consume the server event stream;
    // whenever a round finishes without the sentinel, continue the session.
    //
    const events = ctx.event.subscribe();
    const iterator = events[Symbol.asyncIterator]();
    let disposed = false;
    const drive = async () => {
      try {
        while (!disposed) {
          const next = await iterator.next();
          if (next.done) break;
          try {
            await handleEvent(next.value);
          } catch (error) {
            console.error("[goal-loop] event handling failed:", error);
          }
        }
      } catch (error) {
        if (!disposed) console.error("[goal-loop] event stream failed:", error);
      }
    };

    const handleEvent = async (event: { type: string; data?: Record<string, unknown> }) => {
      const data = (event.data ?? {}) as { sessionID?: string; reason?: string };

      // Provider/model failure closes the loop rather than spin-retrying.
      if (event.type === "session.execution.failed" && data.sessionID) {
        const state = goals.get(data.sessionID);
        if (state && !state.closed) await closeLoop(data.sessionID, state);
        return;
      }

      // A user interrupt pauses the loop. Shutdown/supersession are runtime
      // lifecycle events and do not mutate the user's saved goal.
      if (
        event.type === "session.execution.interrupted" &&
        data.reason === "user" &&
        data.sessionID
      ) {
        const state = goals.get(data.sessionID);
        if (state && !state.closed) {
          state.paused = true;
          state.certified = false;
          await rename(data.sessionID, pausedTitleFor(state.goal));
        }
        return;
      }

      if (event.type !== "session.idle" || !data.sessionID) return;
      const sid = data.sessionID;
      const state = goals.get(sid);
      if (!state || state.closed || state.paused || state.driving) return;

      state.driving = true;
      try {
        let text: string;
        if (state.round >= maxRounds) {
          await closeLoop(sid, state);
          text =
            `[GOAL LOOP ABORTED] Round limit (${maxRounds}) reached without a completion ` +
            `sentinel for goal:\n${state.goal}\nThe loop is now closed; no further continuations will be issued.`;
        } else if (!state.certified) {
          text =
            `[GOAL LOOP] Your previous round ended WITHOUT calling \`${CERT_TOOL}\`. ` +
            `That is a protocol violation; the harness has continued you automatically.\n\n` +
            `${protocolPrompt(state)}\n\nContinue working toward the goal now, and end this reply with a \`${CERT_TOOL}\` call.`;
        } else {
          text =
            `[GOAL LOOP] Round ${state.round} certified incomplete; continuing.\n\n` +
            "Address the reported gap, then end your reply with a `" +
            CERT_TOOL +
            "` call (complete:true ONLY when the goal is verifiably met).";
        }

        state.certified = false;
        state.round += 1;
        await ctx.session.synthetic({ sessionID: sid, text });
      } catch (error) {
        // Never let the driver crash the session; drop the loop instead.
        console.error("[goal-loop] continuation failed:", error);
        await closeLoop(sid, state);
      } finally {
        state.driving = false;
      }
    };

    const task = drive();

    // Released when the plugin is disabled, reloaded, or shut down.
    return async () => {
      disposed = true;
      await iterator.return?.();
      await task.catch(() => {});
    };
  },
});
