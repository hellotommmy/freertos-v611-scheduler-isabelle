# Nested-tick rel-spec overlay algebra milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This milestone closes only rung 1 of the nested-tick staircase.  The probe has
an exclusive child-session directory and directly extends
`EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated`; the leaf declares
no side `sessions`.

## Checked results

- `tick_port_overlay` changes exactly the proof-port critical-depth and
  interrupt-mask fields.  Its selector, idempotence, and missed-tick-update
  commutation equations are checked for arbitrary 32-bit `depth` and
  `irq_mask` values, including the nested `1/1` instance.
- `tick_port_overlay_rel_post_state_iff` proves that the graph relation on
  post-states is exactly the image of the overlay function.
- `tick_port_overlay_rel_spec_iff_run` and
  `tick_port_overlay_bisim_iff_run` reduce `rel_spec` and `rel_spec_monad` to
  exact run-image commutation for every concrete shadow state.
- The graph bisimulation is closed under `yield`, invariant `gets`, invariant
  `guard`, commuting `modify`, invariant `condition`, and `bind`.
- The suspended missed-tick increment branch commutes with the overlay.
  `vTaskIncrementTick_tick_port_overlay_bisim_from_unlocked` therefore reduces
  whole-tick transport to one explicit assumption about the unlocked named
  source; it does not discharge that assumption.

No scheduler relation was weakened.  In particular, this rung does not equate
managed and live domains, fix a delayed-list cursor, replace modular word
arithmetic by natural arithmetic, or normalise the nested `1/1` cutpoint to a
public `0/0` state.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe`;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- wrapper: one Isabelle lane (`-j 1`) with a 300-second outer lifecycle bound;
- first cold attempt: `20260811Tnested-tick-rel-spec-01-cold`, exit 2,
  `timed_out=false`, 5.068 s; it exposed the central-ROOT side-session parsing
  dependency before any probe command ran;
- first theory-checking attempt:
  `20260811Tnested-tick-rel-spec-02-session-root`, exit 1,
  `timed_out=false`, 39.086 s; it built the direct parent and found the first
  probe type error;
- final green run: `20260811Tnested-tick-rel-spec-09-guard-top`, exit 0,
  `timed_out=false`, `quick_and_dirty=false`, wrapper 27.708 s and Isabelle
  leaf 3 s.

SHA-256 evidence:

- theory:
  `5E2048444F0C641C83E4B5B854CDAE8914B5B63F91386FBF49D0B6E733A6416B`;
- green command:
  `3B7C5DAE9497ED9C0074CA18CEB82BA66F291303A3D43D26903AD86CFF526C20`;
- green status:
  `1D6CA3087F01FD09397EFB6F067A2C68F3EFE02B52BE743226E92300EB5C22F9`;
- green stdout:
  `6A926F096B05FD92C61F4C3EEFAF16F324ADE75E46295201BF3C0170EC17894E`;
- green stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

## Exact next semantic rule

The first remaining rule is exactly:

```isabelle
tick_port_overlay_bisim depth irq_mask one_due_tick_unlocked_source
```

It is rung 2 (unlocked generated-source self-bisimulation), not part of this
milestone.  Consequently this milestone does not claim that the protected
overlay transfer, one missed-replay body, replay horizon, pending drain,
managed Resume gate, or universal `xTaskResumeAll` is proved.
