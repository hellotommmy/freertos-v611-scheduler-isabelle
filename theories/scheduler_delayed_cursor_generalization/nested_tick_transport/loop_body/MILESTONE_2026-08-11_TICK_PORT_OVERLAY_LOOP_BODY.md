# Tick-port overlay loop-body milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the named exception-aware generated loop
body.  It does not prove the enclosing `whileLoop`, `finally`, prefix
composition, or the whole generated unlocked tick.

## Checked result

For arbitrary proof-port words and arbitrary TCB pointer, with no state,
pointer, heap, list, due-branch, success, or termination precondition:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_loop_body_source pxTCB)
```

The source is checked in its actual three-part order:

1. `liftE` of the Generic-item and TCB constant guards;
2. the tick/key condition whose branches are `throw ()` and `skip`;
3. `liftE` of the unconditional Generic-item `vListRemove'` followed by the
   already checked after-Generic composition.

The first two guards are state-independent.  The condition reads only
`xTickCount_'` and the Generic key through `t_hrs_'`, both exact overlay
frames.  Its exception branch is `yield (Exn ())`, while its normal branch is
`yield (Result ())`; both are covered directly by the universal `yield`
closure.  The final remove and continuation reuse their unconditional green
theorems.  Consequently guard failure and the early throw are matched on both
sides without pointer/list validity, due-branch, successful-execution, or
termination premises.

The outcome relation is explicit and load-bearing: `tick_port_overlay_bisim`
uses equality on the complete monadic outcome, and relational bind uses
`rel_exception_or_result (=) (=)`.  Exception/result tags and their values are
therefore preserved exactly rather than merely relating final states.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run establishes `hyps = 0` and
`prems = 0`; the theory contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-loop-body-01-cold`, exit 0,
  `timed_out=false`, wrapper 63.566 s, rebuilt parent 8 s, and leaf theory 2 s.

SHA-256 evidence for the green checker:

- theory:
  `31F17F86EDB82F5D17BBBD5FB144A8E2DFCAB1B0E58B5A039A390EC9B13373FB`;
- command:
  `03BBEB75DE27A1EF013DE799203623CC3A84DF5D376BEDDE68F3DEEC299523CE`;
- status:
  `1622DFEF0AAD145F5F925AD7525FDB7E496F2DD789F76E805DE0DDEC34063A0D`;
- stdout:
  `B9DDF196CF09145D4C95C083E92ABD21DE360FAA625E3584293DD5F56CDB5661`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline `c7150e6` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining rule is the loop closure for an arbitrary initial cursor:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
    one_due_tick_loop_body_source initial)
```

Only after that rule should the staircase compose the generated `finally`, the
unlocked prefix, and eventually the whole unlocked tick.
