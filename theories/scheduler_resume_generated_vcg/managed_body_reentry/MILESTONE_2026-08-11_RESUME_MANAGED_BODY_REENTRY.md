# Resume managed body re-entry transaction — 2026-08-11

Baseline: `ecbbe9c` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child combines the exact generated pending-head body with the
managed re-entry phase theorem.  Under exactly the managed phase and literal
head equation, it returns:

- the exact next-head pointer for `rest` and the source's conditional runtime
  yield accumulator;
- the exact ready-inserted concrete state;
- the literal drained `CursorGeneralStrongResumePendingManagedPhaseRel` for
  `resume_one_pending_abs t a`; and
- the exact task-tail equation for the drained context.

The runtime accumulator `y` remains a source-loop value.  It is not identified
with the quiet post snapshot's `rps_local_yield`, which remains false as
required by `resume_pending_entry_rel`.  The richer original-transaction
loop-head/yield-check ghost remains available from the underlying checked body
theorem but is not part of this minimal recursive interface.

No generated VCG is reopened, and no theorem uses the legacy
`resume_pending_gate_entry_rel`, a managed/live equality, or a global
Generic-owner equation.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_reentry_exact` | 2 | 0 |

The embedded ML ledger checks exactly `2`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Body_Reentry` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Gate_Phase`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run exposed only a missing `show ?thesis` before an `apply` block.
The bounded repair added that proof-mode command without changing the theorem.

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-body-reentry-01-thin-transaction` | 1 | 220.587 s | proof-mode structure red |
| `20260811Tresume-managed-body-reentry-02-show-thesis` | 0 | 213.282 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `E479848AE159847B3D8AE223F9D552E45BAD229CA329F6BDE94AAC91BC72A993` |
| `command.txt` | `2E37C17CB01E006D8994CBDCBE9AC0B41064C7436F10E01E8F30BD8F70BC8363` |
| `status.txt` | `FD6500EBE4C6DB9C5F41FF3E6C893543784AF8F1345FF458DF3C1F33D13EDAF9` |
| `stdout.log` | `F0AE8B0A2634564A93209FD77B91A4839245492F9A900B55EA713C1AEEA37074` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next child performs a list induction on `rpc_tasks C`, repeatedly applying
this transaction theorem.  It must return a managed phase with an empty task
list and prove the modular runtime accumulator law
`final_y != 0 <-> y != 0 or requires_yield`, while keeping the quiet ghost
snapshot separate from that runtime word.
