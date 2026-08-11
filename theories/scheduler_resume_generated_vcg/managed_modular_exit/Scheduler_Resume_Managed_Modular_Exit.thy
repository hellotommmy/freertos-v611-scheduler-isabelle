theory Scheduler_Resume_Managed_Modular_Exit
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Yield.Scheduler_Resume_Managed_Modular_Yield"
begin

definition resume_managed_exit_critical_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "resume_managed_exit_critical_state c =
     scheduler_port_overlay (0 :: 32 word) (0 :: 32 word) c"

lemma resume_managed_eal6_port_exit_critical_exact:
  assumes depth:
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 1"
  shows
    "Scheduler_V611_Tick_Translation.eal6_port_exit_critical' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = resume_managed_exit_critical_state c\<rbrace>"
  unfolding Scheduler_V611_Tick_Translation.eal6_port_exit_critical'_def
    resume_managed_exit_critical_state_def scheduler_port_overlay_def
  apply runs_to_vcg
  subgoal using depth by (cases c) simp
  subgoal using depth by contradiction
  subgoal premises p
  proof -
    have positive:
      "(0 :: 32 word) <
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c"
      using depth by simp
    have nonpositive:
      "\<not> ((0 :: 32 word) <
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c)"
      using p by blast
    have False using nonpositive positive by contradiction
    then show ?thesis ..
  qed
  subgoal premises p
  proof -
    have positive:
      "(0 :: 32 word) <
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c"
      using depth by simp
    have nonpositive:
      "\<not> ((0 :: 32 word) <
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c)"
      using p by blast
    have False using nonpositive positive by contradiction
    then show ?thesis ..
  qed
  done

lemma CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_exit_criticalD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D (1 :: 32 word) irq_mask c a managed termination external"
  shows
    "CursorGeneralStrongSchedulerModularEndpointRel D
       (resume_managed_exit_critical_state c) a
       managed termination external"
proof -
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) irq_mask c (normalize_yield_count_abs a)
       managed termination external"
    and counter:
      "yield_count_mod_rel
         (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
         (sa_yield_count a)"
    using entry
    by (simp_all add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
  obtain c0 where overlay:
      "c = scheduler_port_overlay (1 :: 32 word) irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 (normalize_yield_count_abs a)
         managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF protected] .
  have endpoint:
    "CursorGeneralStrongSchedulerEndpointRel
       D c0 (normalize_yield_count_abs a)
       managed termination external"
    using public
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickPublicEntryRel_iff_endpoint_pending)
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c0 (normalize_yield_count_abs a) managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using endpoint
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  have boundary: "scheduler_boundary_rel c0"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have depth0:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c0 = 0"
    and irq0:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c0 = 0"
    using boundary
    by (simp_all add: scheduler_boundary_rel_def)
  have public_self:
    "scheduler_port_overlay (0 :: 32 word) (0 :: 32 word) c0 = c0"
    using scheduler_port_overlay_current_id[of c0] depth0 irq0
    by simp
  have exit_state:
    "resume_managed_exit_critical_state c = c0"
    using overlay public_self
    by (simp add: resume_managed_exit_critical_state_def)
  have counter0:
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c0)
       (sa_yield_count a)"
    using counter overlay by simp
  show ?thesis
    using endpoint counter0 exit_state
    by (simp add: CursorGeneralStrongSchedulerModularEndpointRel_def)
qed

theorem CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_exit_critical:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D (1 :: 32 word) irq_mask c a managed termination external"
  shows
    "Scheduler_V611_Tick_Translation.eal6_port_exit_critical' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = resume_managed_exit_critical_state c \<and>
       CursorGeneralStrongSchedulerModularEndpointRel
         D t a managed termination external\<rbrace>"
proof -
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) irq_mask c (normalize_yield_count_abs a)
       managed termination external"
    using entry
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
  have depth:
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 1"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_portD[
      OF protected]
    by simp
  note source = resume_managed_eal6_port_exit_critical_exact[OF depth]
  note endpoint =
    CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_exit_criticalD[
      OF entry]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using endpoint by blast
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ = if null (Thm.hyps_of th) then ()
              else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ = if actual = expected then ()
              else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "managed exit-critical exact source" 1
    @{thm resume_managed_eal6_port_exit_critical_exact}
  val _ = audit_exact "modular protected exit to endpoint" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_exit_criticalD}
  val _ = audit_exact "generated modular exit-critical" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_exit_critical}
\<close>

end
