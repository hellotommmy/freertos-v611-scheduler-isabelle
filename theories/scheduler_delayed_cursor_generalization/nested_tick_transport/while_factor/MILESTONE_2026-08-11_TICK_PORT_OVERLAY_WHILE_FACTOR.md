# Tick-port overlay while-factor milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the generic relational `whileLoop` factor.
It does not prove termination, functional correctness, the enclosing
`finally`, the unlocked prefix, or the whole generated unlocked tick.

## Checked result

For arbitrary proof-port words and arbitrary initial TCB pointer, with no
non-null, body-success, termination, state, heap, pointer, or list premise:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
    one_due_tick_loop_body_source initial)
```

The checked generic while rule fixes all three relations precisely:

- accumulator relation: equality on TCB pointers;
- state relation: `tick_port_overlay_rel depth irq_mask`;
- body outcome relation: `rel_exception_or_result (=) (=)`.

The loop condition depends only on the accumulator, so overlay invariance is
definitionally `refl`.  The body obligation is exactly the already checked
unconditional Loop Body theorem for every accumulator.  The rule has no
termination, `initial \<noteq> NULL`, or body-success premise; nontermination
and exceptional outcomes are retained by `rel_spec_monad_whileLoop` rather
than excluded from the statement.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run establishes `hyps = 0` and
`prems = 0`; the theory contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-while-factor-01-cold`, exit 0,
  `timed_out=false`, wrapper 63.072 s, rebuilt parent 8 s, and leaf theory 2 s.

SHA-256 evidence for the green checker:

- theory:
  `47E7BC84133B8565415595C8CE40ADB5A90042B3179CB50DA0FF4B5893B47628`;
- command:
  `D757B4C28DFDA8E1967F3D42EF0E6686CE6581BB1366A9599FF9CB2084B6E438`;
- status:
  `ADDED2019266DCA1213A32C6391A055124A446E36B565929DBD3EC53D0D2612E`;
- stdout:
  `392F4095FE9D9D86EE22F0CEF2F5762676B9E8FA8B8A3CDEF3122CDD3789423F`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline `2863e0d` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining rule is the generated `finally` factor:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (finally (do {
     pxTCB \<leftarrow> whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
       one_due_tick_loop_body_source initial;
     skip
   }))
```

The whole unlocked source remains outside this milestone.
