# Cursor-general managed terminal staircase

Status: **machine-checked with `quick_and_dirty = false` on 2026-08-10**.

All nine exclusive sessions completed green in the recorded dependency order,
from `20260810Tcursor-general-terminal-empty-state-01` through
`20260810Tcursor-general-terminal-future-finally-01`.  The original static
freeze notes below are retained as an audit trail.

## Frozen theory files

| Theory file | Lines | SHA-256 |
|---|---:|---|
| `empty_state/Scheduler_Delayed_Cursor_General_Terminal_Empty_State.thy` | 76 | `CB78595A1D6949A3729B21B20D9F6ACDE3CFDD219C6BF39C2C756B15123D6F5E` |
| `empty_result/Scheduler_Delayed_Cursor_General_Terminal_Empty_Result.thy` | 163 | `4FDAE2B6D05AD1A9E5329F8F4D97DC944A0291E321090A3A4C0C97BD15307C8D` |
| `empty_bare/Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare.thy` | 96 | `E95E461F5682DCC65BB2C2DD0505D364F3782CE203809D188E468468726615FD` |
| `empty_finally/Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally.thy` | 49 | `A50BD1D4E8774CD77848A6D5290EF56ECB0AFE521B5296FA503E06B24CFDB598` |
| `future_ready/Scheduler_Delayed_Cursor_General_Terminal_Future_Ready.thy` | 199 | `A3AF1896ED6E6A08FA760371F01D4E8AFF18F2DF351395F3BAC059D583D12A39` |
| `future_state/Scheduler_Delayed_Cursor_General_Terminal_Future_State.thy` | 108 | `48559D9C07B807240B7739680F13D9252609936190B648D0CCC2724745B5708D` |
| `future_result/Scheduler_Delayed_Cursor_General_Terminal_Future_Result.thy` | 124 | `7362FC29F85039ED050790A55CBED2B03728557FDF96B64D8C8A8023C892ABDF` |
| `future_bare/Scheduler_Delayed_Cursor_General_Terminal_Future_Bare.thy` | 248 | `C9E81D23B77EDD357733ACA7514D55E6BF7C202746A93DEA873348B88D754C7A` |
| `future_finally/Scheduler_Delayed_Cursor_General_Terminal_Future_Finally.thy` | 68 | `CA0B8F1FB934A63561413E6DE8426578BE47E8290D49E2903029C1E0093D44CC` |

## Exact ROOT and checker order

Register one session per directory, with each session inheriting the preceding
session.  The exact order is:

1. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_State`
   - parent:
     `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core`
2. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Result`
   - parent: General Terminal Empty State
   - additional session dependency:
     `EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Terminal`
3. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare`
   - parent: General Terminal Empty Result
4. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally`
   - parent: General Terminal Empty Bare
5. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Ready`
   - parent: General Terminal Empty Finally
6. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_State`
   - parent: General Terminal Future Ready
7. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Result`
   - parent: General Terminal Future State
8. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Bare`
   - parent: General Terminal Future Result
9. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Finally`
   - parent: General Terminal Future Bare

Use `quick_and_dirty = false`, `parallel_proofs = 0`, and the repository's
bounded single-lane wrapper.  Do not build a descendant until its immediate
parent is green and frozen.

## Principal theorem interface

The two pure state adapters are:

- `CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_full_state`;
- `CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_full_state`.

Each is followed by `result_full`, `bare_loop_full`, and `finally_full` with
the same branch-specific prefix.  Every public adapter assumes the real
`CursorGeneralDueLoopStrongHeadRel` with independent symbolic
`generic_raw`, `generic_abs`, `event_raw`, and `event_abs`, plus the unchanged
managed gate, selector, and generated-root equality.  Empty and future
endpoints contain `CursorGeneralStrongDuePrefixLoopHeadRel`; no old cursor
policy is used to reconstruct them.

The only occurrence of `canonicalize_scheduler_cursors` is in the future-ready
lemma's abstract core/time proof shadow.  No raw family, abstract family, or
heap is canonicalised or replaced.  Source result, bare-loop exception, and
finally normalisation facts are reused without changing the concrete state.

## Static audit

- all nine theories have one `begin` and one `end`;
- explicit `proof` and `qed` counts balance;
- every theory is below 350 lines and occupies an exclusive directory;
- no `sorry`, `oops`, `admit`, axiom declaration, oracle, Sledgehammer, or
  quick-and-dirty marker occurs;
- there is no list-cursor `None`/tail premise and no General-to-old adapter;
- task, tick, future key, raw roots, list families, cursor positions, decoder,
  managed domain, termination ring, and protected external roots remain
  symbolic.  Empty/future list shapes are the two semantic terminal branches,
  not fixed test instances.
