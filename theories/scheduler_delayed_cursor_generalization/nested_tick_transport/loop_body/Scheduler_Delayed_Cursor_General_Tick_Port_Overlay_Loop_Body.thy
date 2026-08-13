theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic"
begin

text \<open>
  The loop body is exception-aware.  The overlay bisimulation relates its
  complete outcome by equality; equivalently, relational bind uses
  @{term "rel_exception_or_result (=) (=)"}.  Thus both the early @{term Exn}
  and every normal @{term Result} are preserved exactly.  Constant guards may
  fail on both sides, and the tick/key condition selects the same throw or
  normal branch because the overlay frames both state reads.
\<close>

theorem one_due_tick_loop_body_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (one_due_tick_loop_body_source pxTCB)"
  unfolding one_due_tick_loop_body_source_def
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     apply (rule tick_port_overlay_bisim_liftE)
     apply (rule tick_port_overlay_bisim_bind)
      subgoal
        apply (rule tick_port_overlay_bisim_guard)
        by (rule refl)
     subgoal
       apply (rule tick_port_overlay_bisim_guard)
       by (rule refl)
     done
  subgoal
    apply (rule tick_port_overlay_bisim_bind)
     subgoal
       apply (rule tick_port_overlay_bisim_condition)
         subgoal
           by (simp only: tick_port_overlay_core_selectors(1,2))
        subgoal by (rule tick_port_overlay_bisim_yield)
       subgoal by (rule tick_port_overlay_bisim_yield)
       done
    subgoal
      apply (rule tick_port_overlay_bisim_liftE)
      apply (rule tick_port_overlay_bisim_bind)
       subgoal by (rule vListRemove_tick_port_overlay_bisim)
      subgoal
        by (rule one_due_tick_after_generic_tick_port_overlay_bisim)
      done
    done
  done

ML \<open>
  val loop_body_bisim =
    @{thm one_due_tick_loop_body_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of loop_body_bisim) then ()
    else error "loop-body overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of loop_body_bisim) then ()
    else error "loop-body overlay bisim has premises"
\<close>

end
