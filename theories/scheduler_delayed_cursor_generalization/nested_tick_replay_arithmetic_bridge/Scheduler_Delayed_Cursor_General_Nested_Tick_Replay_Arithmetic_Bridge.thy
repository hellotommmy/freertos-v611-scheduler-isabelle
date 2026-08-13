theory Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Arithmetic_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Horizon_Abs.Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Horizon_Abs"
begin

text \<open>
  Protected replay states differ from a public cursor-general snapshot only in
  the two proof-port words.  The three scalar observations below therefore
  remain pinned for arbitrary depth and interrupt mask.  In particular, this
  theorem does not assert that the current generated arithmetic is defined.
\<close>

lemma
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_replay_scalar_pinsD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows a) \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
proof -
  obtain c0 where concrete:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where full:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF public] .
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using full
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have scalar: "scheduler_managed_scalar_rel c0 a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have pins0:
    "Scheduler_V611_Parse.globals.xTickCount_' c0 = sa_tick a \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c0 =
       of_nat (sa_overflows a) \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c0) =
       sa_missed_ticks a"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def)
  show ?thesis using concrete pins0 by simp
qed

theorem
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_arithmetic_defined_iff:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
     resume_tick_arithmetic_defined_abs a"
proof -
  have pins:
    "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows a) \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_replay_scalar_pinsD[
        OF entry])
  have tick:
      "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a"
    and overflow:
      "Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
        of_nat (sa_overflows a)"
    and missed:
      "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
        sa_missed_ticks a"
    using pins by blast+
  show ?thesis
    unfolding generated_unlocked_tick_arithmetic_defined_def
      resume_tick_arithmetic_defined_abs_def
    apply (subst tick)
    apply (subst overflow)
    apply (subst overflow)
    by simp
qed

ML \<open>
  fun audit_0_1 label th =
    let
      val hyps = Thm.hyps_of th
      val prems = Thm.prems_of th
      val _ =
        if null hyps then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        (case prems of
           [_] => ()
         | _ => error
             (label ^ " expected exactly one premise, found " ^
              Int.toString (length prems)))
    in () end

  val _ = audit_0_1 "protected replay scalar pins"
    @{thm
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_replay_scalar_pinsD}
  val _ = audit_0_1 "protected replay arithmetic iff"
    @{thm
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_arithmetic_defined_iff}
\<close>

end
