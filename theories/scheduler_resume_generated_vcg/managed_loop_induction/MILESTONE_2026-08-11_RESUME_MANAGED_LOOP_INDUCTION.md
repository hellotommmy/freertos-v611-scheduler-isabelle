# Resume managed pending-loop induction — 2026-08-11

Baseline: `267e80c` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child lifts the checked managed head transaction to an
arbitrary finite `rpc_tasks C` list.  The auxiliary theorem uses exactly the
managed phase relation and the literal task-list equation; the public theorem
specializes the equation by reflexivity.  The final post supplies:

- `Result (NULL, yw)` after the generated `whileLoop`;
- a fresh existential managed phase relation over
  `drain_pending_nodes_abs (map Event ts) a`;
- an empty post task list;
- exact frames for `rpc_live`, `rpc_current_priority`, and `rpc_priority`; and
- the exact runtime accumulator value
  `yw = (if there is a processed priority trigger then 1 else y)`.

The exact value law is intentionally stronger than a nonzero-only encoding:
the generated caller later compares the word with literal `1`.  It also
preserves arbitrary incoming values when no task triggers a yield, so an empty
list with `y = 7` still returns `7`.  The runtime word is not identified with
`rps_local_yield`; every recursive managed phase re-enters through the quiet
drained snapshot.

The proof reuses the checked zero-premise `drain_pending_nodes_abs_map_Event`
bridge internally, while the public API exposes the canonical node-drain
vocabulary directly.  This rung does not use the legacy
`resume_pending_gate_entry_rel`, a managed/live equality, a global owner
equation, or an extra roots premise.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains_aux` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains` | 1 | 0 |

The embedded ML ledger checks exactly `2/1`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Induction` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Body_Reentry`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The conclusive repository-wrapper runs used a 600-second
lifecycle budget and invoked Isabelle with `-o quick_and_dirty=false -j 1`.

The initial 300-second controller attempt rebuilt only the cold parent.  Its
controller exited before writing status or stdout, so it is explicitly not a
theorem verdict; the exact Java PID and its descendant process tree were
validated and fail-closed before any rerun.  A separate parent warm-up then
finished with exit `0` in `514.086` seconds.

The bounded proof repairs followed the first error only.  The weak Run04
nonzero contract went green but was not promoted: it was strengthened to the
exact accumulator value before the final checker.

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-loop-induction-01-list-fold` | no verdict | 324.1 s outer timeout | cold parent only; child worker not started; fail-closed cleanup |
| `20260811Tresume-managed-loop-induction-parent-warm-01` | 0 | 514.086 s | parent heap warmed |
| `20260811Tresume-managed-loop-induction-02-hot-list-fold` | 1 | 526.473 s | first red: Nil witness automation |
| `20260811Tresume-managed-loop-induction-03-explicit-nil-witnesses` | 1 | 535.574 s | first red: floated Nil phase existential |
| `20260811Tresume-managed-loop-induction-04-nil-conj-split` | 0 | 557.822 s | weak nonzero skeleton green; not promoted |
| `20260811Tresume-managed-loop-induction-05-exact-yield-word` | 1 | 527.275 s | first red: exact value moved outside witnesses |
| `20260811Tresume-managed-loop-induction-06-exact-value-conj-split` | 1 | 520.887 s | first red: stale Result-era `refl` |
| `20260811Tresume-managed-loop-induction-07-phase-existential-split` | 0 | 519.035 s | exact-value theorem green with helper-fold vocabulary; leaf 4 s |
| `20260811Tresume-managed-loop-induction-08-canonical-node-drain` | 0 | 522.404 s | final canonical node-drain API green; leaf 6 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `A8508265586BDE28A839C2F1E38E700A3D6335BB5B3CAAFD3FD851F227E373C6` |
| `command.txt` | `24A0DEA076FF479033F690E81937774CF93411798E97FCE280C729A6F5F3A3A9` |
| `status.txt` | `B9C9FD5BAE689B76CD91CB10F1DDA54BF498F53090D6D522450362997FEB2B0D` |
| `stdout.log` | `F707E4CA828EE4BAC275FBEA900A8973540ED062734EF5887D994C8141F4F21E` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The next sole-parent pure child uses the managed pending-ring equality to
rewrite the checked node drain to `drain_pending_abs a`, relates the exact
trigger predicate to
`resume_pending_requires_yield a` in both current-task cases, and exports the
empty protected tick-entry/control-frame facts needed by missed-tick replay.
It remains managed-only and must not call the legacy gate relation.
