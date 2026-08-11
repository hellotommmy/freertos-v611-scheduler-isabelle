# Tick-port overlay top-ready-tail milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the named generated top-ready-tail factor. It
does not compose `one_due_tick_after_generic_source`, enter any larger prefix
or loop body, unfold `whileLoop`/`finally`, or claim the whole unlocked tick.

## Checked result

For arbitrary proof-port words and arbitrary TCB pointer, with no state,
branch, priority, heap, root, pointer, or list-validity precondition:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_top_ready_tail_source pxTCB)
```

The proof uses `one_due_tail_source_split`.  Its delayed remainder is checked
first as an unconditional local leaf: delayed-root guard, delayed-count
condition, the nonempty branch's head and sentinel guards plus owner read, the
empty branch's `NULL`, and the final pointer coercion.  Each obligation uses
only `bind`, `guard`, `condition`, `gets`, or `yield` closure and the exact
`t_hrs_'` / `pxDelayedTaskList_'` selector frames.

The top-ready proof then checks the top-priority condition, its word-valued
record update (using updater commutation rather than a natural-number
specialisation), both guards, ready-array selection, the already checked
unconditional `vListInsertEnd'` leaf, and the delayed remainder.  Guard failure
is therefore matched on both sides.  No success, termination, valid-pointer,
valid-list, task-priority, root, heap-layout, or `runs_to` premise is added.

The final theory contains no `oops` or `sorry`.  Its ML object audit fails the
session unless both `Thm.hyps_of` and `Thm.prems_of` of the final theorem are
empty.  The green run therefore establishes `hyps = 0` and `prems = 0` from
the theorem object, not merely from the printed statement.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Cold-import boundary and checker record

An import-only diagnostic established that the original dual-heap leaf shape
was unsuitable for a 60-second semantic child:

- `20260811Tnested-tick-top-ready-tail-05-import-only-bisect` used Event
  Dispatch as parent and Prefix Source Factors as a side session, with both
  prospective theorem proofs temporarily replaced by `oops`;
- it still ended at the ROOT `timeout=60` boundary, exit 142,
  `timed_out=false` at the 300-second wrapper level, elapsed 110.435 s;
- status SHA-256:
  `E22CB234B1443D4EA3E5E78FF878F835355C977FEE815DD88DE69C6E389B2F1C`;
- stdout SHA-256:
  `DEF08A1A0073D3130EB55A7DA0417821506924AE3252687A50A14930D9FE7C01`.

That run is infrastructure evidence, not a proof failure.  The discarded
diagnostic source was not staged.  The checked topology moves the cold merge
into an exclusive compatibility heap:

- Join session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail_Join`;
- Join sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Factors`;
- Join side session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch`;
- Join options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=180`;
- Join checker:
  `20260811Tnested-tick-top-ready-tail-06-join-cold`, exit 0,
  `timed_out=false`, wrapper 51.844 s and Join theory 4 s;
- Join theory SHA-256:
  `5A1A63983F8354ABFD0341BA7E8874D8B7BFA408B8FB5C15146F94BB87402775`;
- Join command/status/stdout SHA-256:
  `FFE942265A6407A449EF8BB30AC5C583C90053DCDC26AB3B1C498F34001ACCA8`,
  `BC36FFF75E8F51771C09D032A1C9E5258C37F34B392F30380E392CF49AA67327`,
  `7A623D848F9087D7BF465661935B5BACD078C0E91370E38E4555C3CA61F0612F`.

The semantic leaf then has exactly one parent and no side sessions:

- child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail`;
- sole parent: the checked Join session above;
- child options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- final checker:
  `20260811Tnested-tick-top-ready-tail-07-proof-first`, exit 0,
  `timed_out=false`, wrapper 61.215 s and Top theory 2 s.

SHA-256 evidence for the final green checker:

- Top theory:
  `E270EA3381C3B608F1F93F47B411B75A851E5EC1DCA099D03E5C5E0B51C5B934`;
- command:
  `652A983CBBA2C33575CE7718579A39DD96C5CF77DDB2076213346C052936F24A`;
- status:
  `EF375E70BEC53B87E8123256F4B59737768D1754E7E1B884C37C8CA9E78AA7A2`;
- stdout:
  `EAAB23D930A528DBE787B7829EAAB1F7766B6DB0B4E88ECDC51D2993D2CA8252`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline `7611f63` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining named composition rule is:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_after_generic_source pxTCB)
```

Only after that composition should the staircase enter unlocked role/prefix
factors, the loop body, `whileLoop`/`finally`, and finally the whole generated
unlocked tick.
