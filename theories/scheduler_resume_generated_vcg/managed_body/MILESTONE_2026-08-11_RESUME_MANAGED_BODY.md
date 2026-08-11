# Resume managed generated body — 2026-08-11

Baseline: `0c91cdd6b13567275d65da8b2cba3007eb9b08fc` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child factors the literal generated pending body into the five
checker-green managed programs: entry guard, two unlinks, ready fragment, yield
join, and post-ready next-head read.  The zero-premise factor equality is then
used to prove the exact end-to-end body result from only the managed phase and
`rpc_tasks C = t # rest`.

The body returns the exact next-head pointer and accumulated yield word, ends
at the exact ready-inserted concrete state, and carries forward:

- post Generic and Event coverage;
- managed task observation and rebuilt cross-storage separation;
- the protected control frame and exact abstract/concrete top;
- the committed `[t]`/`rest` loop-head invariant; and
- the sound accumulated nonzero-yield law.

It does not claim a re-entry managed gate, a full post scheduler snapshot,
global unlinking after ready insertion, or direct word/local-yield equivalence.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `resume_pending_generated_body_managed_factor` | 0 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_exact` | 2 | 0 |

The embedded ML ledger is `0/2`, with zero hidden hypotheses throughout.

## Checker topology and evidence

The exclusive session `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Body` has
sole parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_TCB_Guard`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-body-01-five-factor-compose` | 0 | 188.264 s | green; parent 9 s, leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `5FB33D211B3E871380BD2131FBEF59F2C5EEDA2DC93CEDCD568F190E9F2E1BDA` |
| `command.txt` | `4A1AED0D0A7FC6C8F7EC84E1E63B0196B7763DFD83306FB10FBF835CDDF30171` |
| `status.txt` | `31AB96F6F9D20C33AAAD3093F25BEEC2A1924FED2790A2090F8384A5F25F179D` |
| `stdout.log` | `4C477D70DE7FEECDA37EDA2C823089027900438DCAFD76E2B1EF4D11B3A13CD5` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

One managed body iteration is now source-exact and relationally classified.
The next semantic rung must reconstruct the parallel managed phase at the
ready-inserted state for `resume_one_pending_abs t a`, with tail `rest`, while
preserving managed/termination/external domains and cursor-general invariants.
It must not fall back to `resume_pending_gate_entry_rel`.
