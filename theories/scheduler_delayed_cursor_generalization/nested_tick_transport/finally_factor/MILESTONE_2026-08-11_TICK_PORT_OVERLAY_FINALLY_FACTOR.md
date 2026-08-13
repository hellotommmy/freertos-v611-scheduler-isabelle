# Tick-port overlay finally-factor milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the generic `finally` factor, first in its
raw source shape and then as the thin named factor used by the outer unlocked
tick decomposition.  It does not prove the unlocked role source, the complete
unlocked prefix, or the whole generated unlocked tick.

## Checked results

For arbitrary proof-port words and arbitrary initial TCB pointer, with no
termination, non-null, success, state, heap, pointer, list, or branch premise:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (finally (do {
     pxTCB \<leftarrow> whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
       one_due_tick_loop_body_source initial;
     skip
   }))
```

The same result is exported in the exact named form needed by the outer
factorisation:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (due_prefix_generated_finally_loop initial)
```

The named corollary unfolds only
`due_prefix_generated_finally_loop_def` and
`due_prefix_generated_bare_loop_def`; it does not unfold the loop body.

The type boundary is exact.  The checked while factor has unit exceptions and
a TCB-pointer normal result.  Monadic bind preserves the unit exception and
maps every normal result through `skip`, yielding unit normal results.  Thus
the inner monad is `(unit, unit, globals) exn_monad`, which instantiates the
same exception/result type required by `tick_port_overlay_bisim_finally`.
Exceptional, normal, and nonterminating behaviours remain related; none is
removed by an added success or termination assumption.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty for both the raw theorem and the named corollary.  The
green run establishes `hyps = 0` and `prems = 0` for both objects.  The theory
contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- raw-factor checker:
  `20260811Tnested-tick-finally-factor-01-cold`, exit 0,
  `timed_out=false`, wrapper 64.915 s, rebuilt parent 8 s, and leaf theory
  2 s;
- final named-factor checker:
  `20260811Tnested-tick-finally-factor-02-named`, exit 0,
  `timed_out=false`, wrapper 53.900 s, and leaf theory 2 s.

SHA-256 evidence for the final green checker:

- theory:
  `37BE3E2824D10B6892B6AE2D916D0E322EF3B882F230BDAA2FE9628DF10ED262`;
- command:
  `09F1E4B649799005DE0A19F157F298E72CCBABD81422EA705B71415FA6B74867`;
- status:
  `089081EC78B20F613C53D406554048D572CDD01D15708728743A966E5FF86602`;
- stdout:
  `B35DE12B10CFB3B9377B3297D56C67E9144270B8317AFD0350059645B5C2D718`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The raw-factor checker status SHA-256 is
`F41BB1667081A3D05C9BC14C77DF9F737A6795C3A6B19C1C03133366A4786EE3`.

The post-run audit against baseline
`4f28532af6338c1aad4834083bb79c19b0a4d0ed` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining universal overlay rule is the outer role-source factor:

```isabelle
tick_port_overlay_bisim depth irq_mask
  generated_unlocked_tick_role_source
```

After that factor, the already checked delayed remainder can be composed via
`generated_unlocked_tick_prefix_source_split`; only then should the complete
prefix and `one_due_tick_unlocked_source` be assembled.  Those rungs remain
outside this milestone.
