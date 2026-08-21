// goal-loop: a deterministic /goal command for OpenCode V2.
//
// Usage:   /goal <description>
// Behavior:
//   1. `/goal` submits your description plus a hidden sentinel token.
//   2. The `context` hook (fired immediately before model dispatch) detects the
//      sentinel in the newest message and arms the loop for that session.
//      Arming is exact — no heuristics on model output.
//   3. Every time the session goes idle, the plugin runs the configured check
//      command. Pass  -> loop ends (success notice posted).
//      Fail          -> the session is re-prompted to keep working, up to
//                       maxIterations rounds.
//
// The model never decides whether to continue; the check's exit code does.
//
// Configuration (optional) — add an explicit entry in opencode.jsonc:
//   {
//     "plugins": [
//       { "package": "./.opencode/plugins/goal-loop.js",
//         "options": { "check": "lake build", "maxIterations": 20 } }
//     ]
//   }
// Without an entry the defaults below apply ("lake build", 20 rounds).

import { execFile } from "node:child_process"

const SENTINEL = "[[goal-loop]]"

export default {
  id: "lastlib.goal-loop",
  async setup(ctx) {
    const options = ctx.options ?? {}
    const check = typeof options.check === "string" ? options.check : "lake build"
    const maxIterations =
      Number.isInteger(options.maxIterations) && options.maxIterations > 0 ? options.maxIterations : 20
    const checkTimeoutMs = Number.isFinite(options.checkTimeoutMs) ? options.checkTimeoutMs : 15 * 60_000
    const fallbackCwd = typeof options.cwd === "string" ? options.cwd : undefined

    let armed = null // { sessionID, iterations } | null
    let checking = false

    const runCheck = (cwd) =>
      new Promise((resolve) => {
        execFile("/bin/sh", ["-c", check], { cwd, timeout: checkTimeoutMs }, (error) => resolve(!error))
      })

    // --- Arm ---------------------------------------------------------------
    // The context hook runs right before each model dispatch. The *last*
    // message is the freshly submitted prompt, so we only inspect that one:
    // this avoids re-arming from the sentinel lingering in older history.
    // We stringify instead of trusting beta message part shapes.
    await ctx.session.hook("context", (event) => {
      const last = event.messages?.[event.messages.length - 1]
      if (last !== undefined && JSON.stringify(last).includes(SENTINEL)) {
        armed = { sessionID: event.sessionID, iterations: 0 }
      }
    })

    // --- Register /goal ----------------------------------------------------
    await ctx.command.transform((commands) => {
      commands.update("goal", (command) => {
        command.description = `Iterate until \`${check}\` passes (max ${maxIterations} rounds)`
        command.template = [
          "$ARGUMENTS",
          "",
          SENTINEL,
          "",
          `You are in a goal loop. The harness will run \`${check}\` after every turn you finish.`,
          "Work toward the goal above. After each round of changes, verify your work yourself;",
          "do not declare success — the harness decides, based on the check's exit code.",
          "Keep each turn focused: make progress, then end the turn so the check can run.",
        ].join("\n")
      })
    })

    // --- Drive the loop ----------------------------------------------------
    const controller = new AbortController()
    const pump = (async () => {
      try {
        for await (const event of ctx.event.subscribe({ signal: controller.signal })) {
          if (event.type !== "session.idle" || !armed || checking) continue
          if (event.data.sessionID !== armed.sessionID) continue

          checking = true
          const sessionID = armed.sessionID
          let passed = false
          try {
            const cwd = event.location?.directory ?? fallbackCwd ?? process.cwd()
            passed = await runCheck(cwd)
          } finally {
            checking = false
          }

          if (!armed || armed.sessionID !== sessionID) continue // re-armed meanwhile

          if (passed) {
            armed = null
            await ctx.session.synthetic({
              sessionID,
              text: `goal-loop: check passed (\`${check}\`). Loop complete.`,
              description: "goal-loop status",
            })
          } else if (armed.iterations + 1 < maxIterations) {
            armed.iterations += 1
            await ctx.session.prompt({
              sessionID,
              text:
                `goal-loop: \`${check}\` still failing (round ${armed.iterations + 1}/${maxIterations}). ` +
                "Diagnose the failure, fix it, and end your turn so the check runs again.",
            })
          } else {
            armed = null
            await ctx.session.synthetic({
              sessionID,
              text: `goal-loop: giving up after ${maxIterations} rounds; \`${check}\` still failing.`,
              description: "goal-loop status",
            })
          }
        }
      } catch (error) {
        if (!controller.signal.aborted) console.error("[goal-loop] event pump failed:", error)
      }
    })()

    return async () => {
      controller.abort()
      await pump.catch(() => {})
    }
  },
}
