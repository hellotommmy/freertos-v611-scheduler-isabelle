# Resume managed pending-loop pure bridges — 2026-08-12

Baseline: `84be463` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive sole-parent child exports the five managed-only pure bridges
needed immediately after the checked arbitrary pending loop:

- the ordered pending-ring equation
  `ring (sa_pending a) = map Event (rpc_tasks C)`;
- the canonical loop post rewritten exactly to `drain_pending_abs a`;
- the exact equivalence between `resume_pending_requires_yield a` and the
  context priority trigger over `rpc_tasks C`;
- for an empty task list, an empty pending ring, the protected `1/1` tick
  entry at the actual concrete state, and exact depth/mask/running pins; and
- the proof-port control frame between any two managed phase states.

The yield proof keeps the `sa_current = None` and `Some current` cases
separate internally.  In the `None` case, the managed gate's current-safety
clause forces the pending ring and task list to be empty; without that step the
priority trigger would be unsound.  The `Some` case uses only the managed
phase alignment's exact current-priority and priority-function equations.

The tick-entry proof constructs the public entry at the protected gate's
shadow `c0`, then uses `c = scheduler_port_overlay 1 1 c0` to establish the
protected entry at the actual state `c`.  It does not confuse the public
`0/0` shadow with the protected `1/1` state.

No theorem calls the legacy `resume_pending_gate_entry_rel`, assumes
`managed = sa_live a`, constrains a cursor policy, or adds a roots premise.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_pending_ringD` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_drain_pending_absD` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_requires_yieldD` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_control_frame` | 2 | 0 |

The embedded ML ledger checks exactly `1/1/1/2/2`, with zero hidden
hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Pure` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Induction`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  Conclusive runs used the repository wrapper with a 600-second
lifecycle budget and Isabelle options `-o quick_and_dirty=false -j 1`.

Run01 was infrastructure-only: `-CentralOnly` omitted the local
`scheduler_resume_generated_vcg` ROOT, so the central graph could not resolve
its imported `Generated_Missed_Loop` session.  It did not load this theory and
is not a theorem red.  Runs02 and 03 used the correct dual-root command and
were repaired strictly at their first mechanical error.

| run | exit | elapsed | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-loop-pure-01-five-managed-bridges` | 2 | 32.079 s | infrastructure only: local resume ROOT omitted; no theory load |
| `20260811Tresume-managed-loop-pure-02-local-root-five-bridges` | 1 | 572.048 s | first proof red: redundant terminal `simp` after `tick_entry_pending_wfI` had already closed the goal |
| `20260812Tresume-managed-loop-pure-03-pending-wf-single-step` | 1 | 515.119 s | first proof red: endpoint existential witnesses were not inferred by broad automation |
| `20260812Tresume-managed-loop-pure-04-explicit-endpoint-witnesses` | 0 | 503.854 s | final green; leaf finished in 5 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `32C4E714F1139AC263AEB719B89801060986121D9954B6EAE8738E0C8B52B401` |
| `command.txt` | `375EE46ABA6234E631E03945B019C10E02DFBBFE5C503280AABA719864FBF581` |
| `status.txt` | `2C2D423A8A48250CA4CE40051CA7A6C734B183AFC6E0411A91C1824C1567F5D0` |
| `stdout.log` | `6A43ACCC7DF81D4BE0B9116BB417B013A971CF5081FF3EAC3C091040CB264D3F` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The next sole-parent operational child weakens the checked managed loop to the
normalized `drain_pending_abs a` post with its exact runtime yield word, then
exports the final protected tick-entry and control-frame consequences.  The
runtime accumulator remains separate from the quiet resume snapshot ghost.
