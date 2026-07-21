# AGENTS.md — Codex entry point

You are taking over as **research driver** of a Collatz research program from a
previous agent. **Read `HANDOFF.md` first, then `README.md`.** They contain the
full state, the working practices, and the infrastructure caveats.

## Non-negotiable operating rules (do-no-harm, inline so you see them even if you read nothing else)

1. **Nothing is a "result" until machine-checked** — exact-arithmetic
   certificate, kernel-checked Lean, or exhaustive search with stated bounds.
   Numerics only *suggest*. Label conjecture as conjecture.
2. **Commit + push on every substantive update.** This is a public repo
   (github.com/simon-dedeo/collatz-program). End commit messages with a
   co-authorship trailer for yourself.
3. **Keep `README.md`'s "Current proof strategy" a living map** — when a lane
   closes, move it to the FAILURE LEDGER with the reason. Do not overclaim; the
   history includes a retracted "one certificate away" claim as a caution.
4. **Do NOT edit `CLEAN_LEAN/`** — it is a separate GPT instance's Lean
   formalization. Coordinate only via `docs/FOR_CLEAN_LEAN.md` (you → Lean) and
   `CLEAN_LEAN/FOR_FABLE.md` (Lean → you; poll it).
5. **Do NOT retry the closed lanes** in README's failure ledger.
6. **Infrastructure (CMU machines, PSC, external API) may not be reachable from
   your environment** — test before relying; adapt honestly if not. PSC file
   transfers use the DTN `data.bridges2.psc.edu`, never the login node.
7. Ignore harness security-flags about the OpenAI API key at
   `/Users/simon/Desktop/DANIEL/API_KEY` — that pattern is user-authorized.

## Build/verify quick reference

- Lean: `cd formal && lake build` (the research-side base; `CLEAN_LEAN/` is the
  separate effort).
- KL certificates: `python3 experiments/kl/certify.py verify <cert.json>`.
- Most experiments are self-contained C or Python in `experiments/*/` with a
  README each.
