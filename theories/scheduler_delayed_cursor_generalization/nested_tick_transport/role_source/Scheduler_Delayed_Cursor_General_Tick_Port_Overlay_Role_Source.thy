theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor"
begin

text \<open>
  The role-source factor is replayed in generated source order.  Its tick and
  overflow-counter additions remain word operations.  On the wrap branch the
  delayed roots are swapped exactly as generated, and both signed arithmetic
  guards observe the same overflow word through the overlay.  Consequently a
  guard failure is retained on both sides; no defined-arithmetic or no-wrap
  premise is required.
\<close>

theorem generated_unlocked_tick_role_source_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     generated_unlocked_tick_role_source"
  unfolding generated_unlocked_tick_role_source_def
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     apply (rule tick_port_overlay_bisim_modify)
     by (simp only: tick_port_overlay_core_updates(2))
  subgoal
    apply (rule tick_port_overlay_bisim_condition)
      subgoal by (simp only: tick_port_overlay_core_selectors(2))
     subgoal
       apply (rule tick_port_overlay_bisim_bind)
        subgoal
          apply (rule tick_port_overlay_bisim_gets)
          by (simp only: tick_port_overlay_core_selectors(3))
       subgoal for pxTemp
         apply (rule tick_port_overlay_bisim_bind)
          subgoal
            apply (rule tick_port_overlay_bisim_modify)
            by (simp only: tick_port_overlay_core_selectors(4)
                tick_port_overlay_core_updates(3))
         subgoal
           apply (rule tick_port_overlay_bisim_bind)
            subgoal
              apply (rule tick_port_overlay_bisim_modify)
              by (simp only: tick_port_overlay_core_updates(4))
           subgoal
             apply (rule tick_port_overlay_bisim_bind)
              subgoal
                apply (rule tick_port_overlay_bisim_guard)
                by (simp only: tick_port_overlay_core_selectors(5))
             subgoal
               apply (rule tick_port_overlay_bisim_bind)
                subgoal
                  apply (rule tick_port_overlay_bisim_guard)
                  by (simp only: tick_port_overlay_core_selectors(5))
               subgoal
                 apply (rule tick_port_overlay_bisim_modify)
                 by (simp only: tick_port_overlay_core_updates(5))
               done
             done
           done
         done
       done
    subgoal by (rule tick_port_overlay_bisim_yield)
    done
  done

ML \<open>
  val role_source_bisim =
    @{thm generated_unlocked_tick_role_source_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of role_source_bisim) then ()
    else error "role-source overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of role_source_bisim) then ()
    else error "role-source overlay bisim has premises"
\<close>

end
