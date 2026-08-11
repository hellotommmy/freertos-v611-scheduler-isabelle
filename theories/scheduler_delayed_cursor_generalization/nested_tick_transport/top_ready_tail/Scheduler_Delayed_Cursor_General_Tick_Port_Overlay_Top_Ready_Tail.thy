theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail_Join.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail_Join"
begin

text \<open>
  The delayed-head remainder observes only the framed scheduler heap and the
  framed live delayed-list root selected by globals.  Every guard therefore
  fails or succeeds on both sides together, for arbitrary globals and without
  pointer or list validity assumptions.
\<close>

lemma one_due_tick_delayed_remainder_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     one_due_tick_delayed_remainder"
  unfolding one_due_tick_delayed_remainder_def
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     apply (rule tick_port_overlay_bisim_guard)
     by (simp only: tick_port_overlay_core_selectors(3))
  subgoal
    apply (rule tick_port_overlay_bisim_bind)
     subgoal
       apply (rule tick_port_overlay_bisim_condition)
         subgoal
           by (simp only: tick_port_overlay_core_selectors(1,3))
        subgoal
          apply (rule tick_port_overlay_bisim_bind)
           subgoal
             apply (rule tick_port_overlay_bisim_guard)
             by (simp only: tick_port_overlay_core_selectors(1,3))
          subgoal
            apply (rule tick_port_overlay_bisim_bind)
             subgoal
               apply (rule tick_port_overlay_bisim_guard)
               by (simp only: tick_port_overlay_core_selectors(3))
            subgoal
              apply (rule tick_port_overlay_bisim_gets)
              by (simp only: tick_port_overlay_core_selectors(1,3))
            done
          done
       subgoal by (rule tick_port_overlay_bisim_yield)
       done
    subgoal by (rule tick_port_overlay_bisim_yield)
    done
  done

text \<open>
  The named source split exposes only the top-priority conditional, its two
  guards, ready-list selection, the already checked universal insert-end leaf,
  and the delayed-head remainder above.  In particular the word-valued
  top-priority assignment is transported exactly; it is not specialised to a
  task, heap, priority, root, or successful execution.
\<close>

theorem one_due_tick_top_ready_tail_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (one_due_tick_top_ready_tail_source pxTCB)"
  apply (subst one_due_tail_source_split)
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     apply (rule tick_port_overlay_bisim_condition)
       subgoal
         by (simp only: tick_port_overlay_core_selectors(1,6))
      subgoal
        apply (rule tick_port_overlay_bisim_modify)
        by (simp only: tick_port_overlay_core_selectors(1)
            tick_port_overlay_core_updates(6))
     subgoal by (rule tick_port_overlay_bisim_yield)
     done
  subgoal
    apply (rule tick_port_overlay_bisim_bind)
     subgoal
       apply (rule tick_port_overlay_bisim_guard)
       by (simp only: tick_port_overlay_core_selectors(1))
    subgoal
      apply (rule tick_port_overlay_bisim_bind)
       subgoal
         apply (rule tick_port_overlay_bisim_guard)
         by (rule refl)
      subgoal
        apply (rule tick_port_overlay_bisim_bind)
         subgoal
           apply (rule tick_port_overlay_bisim_gets)
           by (simp only: tick_port_overlay_core_selectors(1))
        subgoal
          apply (rule tick_port_overlay_bisim_bind)
           subgoal by (rule vListInsertEnd_tick_port_overlay_bisim)
          subgoal
            by (rule
                one_due_tick_delayed_remainder_tick_port_overlay_bisim)
          done
        done
      done
    done
  done

ML \<open>
  val top_ready_tail_bisim =
    @{thm one_due_tick_top_ready_tail_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of top_ready_tail_bisim) then ()
    else error "top-ready-tail overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of top_ready_tail_bisim) then ()
    else error "top-ready-tail overlay bisim has premises"
\<close>

end
