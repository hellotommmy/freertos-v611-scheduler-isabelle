theory Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay.Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec"
begin

text \<open>
  The protected-entry development and the whole generated-tick development
  use separately named copies of the same proof-port overlay.  This child
  makes that equality explicit, closes the scheduler-named bisimulation, and
  removes only that premise from the protected transport theorem.
\<close>

lemma scheduler_port_overlay_eq_tick_port_overlay:
  "scheduler_port_overlay = tick_port_overlay"
  apply (rule ext)
  apply (rule ext)
  apply (rule ext)
  by (simp add: scheduler_port_overlay_def tick_port_overlay_def)

lemma scheduler_port_overlay_rel_eq_tick_port_overlay_rel:
  "scheduler_port_overlay_rel depth irq_mask =
   tick_port_overlay_rel depth irq_mask"
  apply (rule ext)
  apply (rule ext)
  by (simp add: scheduler_port_overlay_rel_def tick_port_overlay_rel_def
      scheduler_port_overlay_eq_tick_port_overlay)

theorem scheduler_port_overlay_tick_bisim_closed:
  "scheduler_port_overlay_tick_bisim depth irq_mask"
  unfolding scheduler_port_overlay_tick_bisim_def
  apply (subst scheduler_port_overlay_rel_eq_tick_port_overlay_rel)
  by (rule vTaskIncrementTick_tick_port_overlay_rel_spec)

corollary
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_transport_closed:
  assumes entry:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask c a managed termination external"
    and unlocked_defined:
      "sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
      \<lbrace>\<lambda>r t.
        r = Result () \<and>
        CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
          D depth irq_mask t (task_increment_tick_modular_abs a)
          managed termination external\<rbrace>"
  by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_complete[
        OF scheduler_port_overlay_tick_bisim_closed entry unlocked_defined])

ML \<open>
  val closed_bisim =
    @{thm scheduler_port_overlay_tick_bisim_closed}
  val protected_transport =
    @{thm
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_transport_closed}

  val _ =
    if null (Thm.hyps_of closed_bisim) then ()
    else error "closed scheduler-port bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of closed_bisim) then ()
    else error "closed scheduler-port bisim has premises"

  val _ =
    if null (Thm.hyps_of protected_transport) then ()
    else error "protected tick transport has hidden hypotheses"
  val _ =
    (case Thm.prems_of protected_transport of
       [_, _] => ()
     | prems =>
         error
           ("protected tick transport expected exactly two premises, found " ^
            Int.toString (length prems)))
\<close>

end
