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
  /** Terminal: sentinel accepted, aborted, cancelled, or errored. */
  closed: boolean;
  /** True while we are driving the session after injecting a continuation. */
  driving: boolean;
};

const goals = new Map<string, GoalState>();

export default Plugin.define({
  id: "lastlib.goal-loop",

  setup: (ctx) => {
    const rawRounds = (ctx.options as { maxRounds?: unknown } | undefined)?.maxRounds;
    const maxRounds =
      typeof rawRounds === "number" && Number.isFinite(rawRounds) && rawRounds > 0
        ? Math.floor(rawRounds)
        : 50;

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
    // /goal command — hands the goal text to the agent, which registers it via goal_set.
    //
    void ctx.command.transform((commands) => {
      commands.update("goal", (command) => {
        command.description =
          "Set a persistent goal; the agent must certify completion (or not) at the end of every round";
        command.template = [
          "Register the following text as my persistent goal by calling the `goal_set` tool now, quoted verbatim:",
          "",
          "$ARGUMENTS",
          "",
          "After registering it, immediately begin working toward the goal.",
          `Remember: every round must end with a \`${CERT_TOOL}\` call.`,
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
          goals.set(toolCtx.sessionID, {
            goal,
            round: 0,
            certified: false,
            closed: false,
            driving: false,
          });
          const replaced = previous && !previous.closed ? " (previous goal discarded)" : "";
          return {
            output: { status: "registered" },
            content: `Goal armed${replaced}. Every round must end with a \`${CERT_TOOL}\` call.`,
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
          if (typeof args.complete !== "boolean") {
            throw new Error("goal_certify requires a boolean `complete`.");
          }
          const summary =
            typeof args.summary === "string" && args.summary.trim().length > 0
              ? args.summary.trim()
              : "(no summary provided)";
          state.certified = true;
          if (args.complete) state.closed = true;
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
      if (!state || state.closed) return;
      event.system.push({ type: "text", text: protocolPrompt(state) });
    });

    //
    // The deterministic continuation driver: consume the server event stream;
    // whenever a round finishes without the sentinel, continue the session.
    //
    const controller = new AbortController();
    const drive = async () => {
      try {
        for await (const event of ctx.event.subscribe({ signal: controller.signal })) {
          try {
            await handleEvent(event);
          } catch (error) {
            console.error("[goal-loop] event handling failed:", error);
          }
        }
      } catch (error) {
        if (!controller.signal.aborted) console.error("[goal-loop] event stream failed:", error);
      }
    };

    const handleEvent = async (event: { type: string; data?: Record<string, unknown> }) => {
      const data = (event.data ?? {}) as { sessionID?: string; reason?: string };

      // Provider/model failure or a user interrupt terminates the loop rather
      // than fighting the user or spin-retrying.
      if (
        event.type === "session.execution.failed" ||
        (event.type === "session.execution.interrupted" && data.reason === "user")
      ) {
        const state = data.sessionID ? goals.get(data.sessionID) : undefined;
        if (state && !state.closed) state.closed = true;
        return;
      }

      if (event.type !== "session.idle" || !data.sessionID) return;
      const sid = data.sessionID;
      const state = goals.get(sid);
      if (!state || state.closed || state.driving) return;

      state.driving = true;
      try {
        let text: string;
        if (state.round >= maxRounds) {
          state.closed = true;
          text =
            `[GOAL LOOP ABORTED] Round limit (${maxRounds}) reached without a completion ` +
            `sentinel for goal:\n${state.goal}\nThe loop is now closed; no further continuations will be issued.`;
        } else if (!state.certified) {
          text =
            `[GOAL LOOP] Your previous round ended WITHOUT calling \`${CERT_TOOL}\`. ` +
            `That is a protocol violation; the harness has continued you automatically.\n\n` +
            `${protocolPrompt(state)}\n\nContinue working toward the goal now, and end this reply with a \`${CERT_TOOL}\` call.`;
        } else if (state.closed) {
          // Sentinel said complete: confirm once and shut the loop quietly.
          text =
            "[GOAL LOOP] Completion sentinel accepted. Goal loop closed — no further certification is required.";
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
        state.closed = true;
      } finally {
        state.driving = false;
      }
    };

    const task = drive();

    // Released when the plugin is disabled, reloaded, or shut down.
    return async () => {
      controller.abort();
      await task.catch(() => {});
    };
  },
});
