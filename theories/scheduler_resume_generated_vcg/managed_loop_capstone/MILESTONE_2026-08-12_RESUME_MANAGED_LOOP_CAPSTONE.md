# Resume managed pending-loop capstone — 2026-08-12

Baseline: `0beea2a` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child packages the checked arbitrary managed pending loop into
the exact one-premise post needed by the outer resume proof.  It uses one
`runs_to_weaken` from the managed loop-induction theorem and preserves:

- the exact `Result (NULL, yw)` result and all eight post witnesses;
- the final managed phase relation over `drain_pending_abs a`;
- the empty post task list and exact live/current-priority/priority frames;
- the exact arbitrary-input accumulator law
  `yw = (if resume_pending_requires_yield a then 1 else y)`;
- the final empty pending ring and protected `1/1` tick entry;
- exact depth, interrupt-mask, and scheduler-running pins; and
- `resume_pending_control_frame c s` between the two actual protected states.

The runtime word remains independent from the quiet resume snapshot ghost.
In particular, if no task triggers and `y = 7`, the exact result stays `7`;
the theorem does not normalize the accumulator to a Boolean word.  The public
tick entry exists only at the hidden `0/0` shadow, while the exported relation
is the protected `1/1` entry at the actual final state.

The proof does not rerun generated VCG, call the legacy
`resume_pending_gate_entry_rel`, assume `managed = sa_live a`, or impose a
cursor, no-wrap, roots, or owner premise.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_pure` | 1 | 0 |

The embedded ML ledger checks exactly one explicit premise and zero hidden
hypotheses.  The theory contains exactly one `runs_to_weaken` occurrence.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Capstone` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Pure`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  Runs used the repository wrapper with a 600-second lifecycle
budget and Isabelle options `-o quick_and_dirty=false -j 1`.

Both bounded repairs were Isar command-mode corrections only; the statement,
witnesses, and proof route never changed.

| run | exit | elapsed | result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-loop-capstone-01-one-phase-exact-post` | 1 | 570.170 s | first red: `apply` issued directly in structured state mode |
| `20260812Tresume-managed-loop-capstone-02-show-before-weaken` | 1 | 222.586 s | first red: structured `fix` issued after tactic prove mode |
| `20260812Tresume-managed-loop-capstone-03-structured-weaken-proof` | 0 | 232.540 s | final green; leaf finished in 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `0C1BCE270E8DA0EC74066CBA0AE46FDCD16711A21EDE39C1560FDBDE50F9CAD7` |
| `command.txt` | `A176F5A422A44F46BC4F26B3D3D293049575F5CD17A53A5E781BC23FF1B6D847` |
| `status.txt` | `7B9F398F14BF7369E43D3A2893D0CBB95AF52F2F06ABC7B725DD96D7380E0250` |
| `stdout.log` | `CC4DCD65F3010842BAF18DDC71814F5F145E2011D88F33227E1D7867BB6E9DBF` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The next sole-parent replay split derives final quietness from the exported
managed phase relation, then composes the checked protected missed-tick safe
loop and first-unsafe no-run theorems.  It must keep success and non-success
separate: the unsafe theorem does not justify an exception or rollback claim.
