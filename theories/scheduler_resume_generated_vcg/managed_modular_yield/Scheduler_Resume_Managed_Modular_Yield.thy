theory Scheduler_Resume_Managed_Modular_Yield
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Clear.Scheduler_Resume_Managed_Modular_Clear"
begin

lemma p2_yield_state_yield_count [simp]:
  "Scheduler_V611_Parse.globals.eal6_port_yield_count_'
      (p2_yield_state c) =
   Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1"
  by (simp add: p2_yield_state_def)

lemma p2_yield_state_port_overlay [simp]:
  "p2_yield_state (scheduler_port_overlay depth irq_mask c) =
   scheduler_port_overlay depth irq_mask (p2_yield_state c)"
  by (simp add: p2_yield_state_def scheduler_port_overlay_def)

lemma core_wf_yield_count_update [simp]:
  "core_wf (a\<lparr>sa_yield_count := n\<rparr>) = core_wf a"
  by (simp add: core_wf_def ring_shape_wf_def role_wf_def
      membership_wf_def time_wf_def ready_cache_wf_def current_wf_def
      delayed_key_agrees_def ready_task_set_def current_delayed_ring_def
      overflow_delayed_ring_def Let_def split: option.splits)

lemma canonicalize_scheduler_cursors_yield_count_update [simp]:
  "canonicalize_scheduler_cursors (a\<lparr>sa_yield_count := n\<rparr>) =
   (canonicalize_scheduler_cursors a)\<lparr>sa_yield_count := n\<rparr>"
  by (cases a)
     (simp add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def)

lemma cursor_general_core_wf_yield_count_update [simp]:
  "cursor_general_core_wf (a\<lparr>sa_yield_count := n\<rparr>) =
   cursor_general_core_wf a"
  by (simp add: cursor_general_core_wf_def ring_shape_wf_def)

lemma scheduler_current_rel_p2_yield_state [simp]:
  "scheduler_current_rel D (p2_yield_state c)
      (a\<lparr>sa_yield_count := n\<rparr>) =
   scheduler_current_rel D c a"
  by (simp add: p2_yield_state_def scheduler_current_rel_def
      split: option.splits)

lemma resume_managed_eal6_port_yield_exact:
  "Scheduler_V611_Delay_Translation.eal6_port_yield' \<bullet> c
   \<lbrace>\<lambda>r t. r = Result () \<and> t = p2_yield_state c\<rbrace>"
  by (rule scheduler_eal6_port_yield_exact)

lemma CursorGeneralStrongSchedulerSnapshotRel_p2_yield_stateI:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel D
       (p2_yield_state c)
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1)\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using snapshot
  unfolding CursorGeneralStrongSchedulerSnapshotRel_def Let_def
  apply (simp only: scheduler_current_rel_p2_yield_state)
  by (simp add:
      p2_yield_state_def
      CursorGeneralStrongManagedDomainRel_def
      strong_generic_role_projection_def strong_event_role_projection_def
      strong_wake_payload_projection_def strong_one_due_snapshot_projection_def
      scheduler_role_rel_def scheduler_managed_scalar_rel_def
      managed_scheduler_view_def scheduler_scalar_rel_def
      scheduler_boundary_rel_def
      TaskObservationRel_def scheduler_managed_task_observation_rel_def)

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_p2_yield_stateI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask (p2_yield_state c)
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1)\<rparr>)
       managed termination external"
proof -
  obtain c0 where overlay:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    full:
      "CursorGeneralStrongVTaskIncrementTickEntryRel
         D c0 a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF public] .
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c0 a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pending: "tick_entry_pending_wf a"
    using full
    by (simp_all add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have counter:
    "Scheduler_V611_Parse.globals.eal6_port_yield_count_' c =
     Scheduler_V611_Parse.globals.eal6_port_yield_count_' c0"
    using overlay by simp
  have snapshot0':
    "CursorGeneralStrongSchedulerSnapshotRel D
       (p2_yield_state c0)
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c0 + 1)\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_p2_yield_stateI[
          OF snapshot])
  have snapshot':
    "CursorGeneralStrongSchedulerSnapshotRel D
       (p2_yield_state c0)
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1)\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using snapshot0' counter by simp
  have pending':
    "tick_entry_pending_wf
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1)\<rparr>)"
    using pending by (simp add: tick_entry_pending_wf_def)
  have full':
    "CursorGeneralStrongVTaskIncrementTickEntryRel D
       (p2_yield_state c0)
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1)\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using snapshot' pending'
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have public':
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D
       (p2_yield_state c0)
       (a\<lparr>sa_yield_count :=
          unat
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c + 1)\<rparr>)
       managed termination external"
    unfolding CursorGeneralStrongVTaskIncrementTickPublicEntryRel_def
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=generic_abs])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=event_abs])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    by (rule full')
  show ?thesis
    unfolding CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def
    apply (rule exI[where x="p2_yield_state c0"])
    using overlay public' by simp
qed

lemma normalize_yield_count_abs_request_yield_step:
  fixes w :: "32 word"
  assumes counter:
    "yield_count_mod_rel w (sa_yield_count a)"
  shows
    "(normalize_yield_count_abs a)
       \<lparr>sa_yield_count := unat (w + 1)\<rparr> =
     normalize_yield_count_abs (request_yield a)"
proof -
  note counter_next = yield_count_mod_rel_request[OF counter]
  show ?thesis
    using counter_next
    by (cases a)
       (simp add: yield_count_mod_rel_def
          normalize_yield_count_abs_def request_yield_def)
qed

lemma CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_p2_yield_stateI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask (p2_yield_state c) (request_yield a)
       managed termination external"
proof -
  let ?w =
    "Scheduler_V611_Parse.globals.eal6_port_yield_count_' c"
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c (normalize_yield_count_abs a)
       managed termination external"
    and counter: "yield_count_mod_rel ?w (sa_yield_count a)"
    using entry
    by (simp_all add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
  have protected_step:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask (p2_yield_state c)
       ((normalize_yield_count_abs a)
         \<lparr>sa_yield_count := unat (?w + 1)\<rparr>)
       managed termination external"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_p2_yield_stateI[
        OF protected])
  have normalized:
    "(normalize_yield_count_abs a)
       \<lparr>sa_yield_count := unat (?w + 1)\<rparr> =
     normalize_yield_count_abs (request_yield a)"
    by (rule normalize_yield_count_abs_request_yield_step[OF counter])
  have protected_normalized:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask (p2_yield_state c)
       (normalize_yield_count_abs (request_yield a))
       managed termination external"
    using protected_step normalized by simp
  have counter':
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_'
         (p2_yield_state c))
       (sa_yield_count (request_yield a))"
    using yield_count_mod_rel_request[OF counter]
    by (simp add: p2_yield_state_def request_yield_def)
  show ?thesis
    using protected_normalized counter'
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
qed

theorem CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "Scheduler_V611_Delay_Translation.eal6_port_yield' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = p2_yield_state c \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D depth irq_mask t (request_yield a)
         managed termination external\<rbrace>"
proof -
  note source = resume_managed_eal6_port_yield_exact[where c=c]
  note preserved =
    CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_p2_yield_stateI[
      OF entry]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using preserved by blast
qed

definition resume_managed_yield_requested ::
  "int \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_managed_yield_requested y a \<longleftrightarrow>
     y = 1 \<or> sa_missed_yield a"

definition resume_managed_yield_caller_abs ::
  "int \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_managed_yield_caller_abs y a =
     (if resume_managed_yield_requested y a
      then a\<lparr>sa_missed_yield := False\<rparr>
      else a)"

definition resume_managed_yield_final_abs ::
  "int \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_managed_yield_final_abs y a =
     (if resume_managed_yield_requested y a
      then request_yield (resume_managed_yield_caller_abs y a)
      else resume_managed_yield_caller_abs y a)"

definition resume_managed_yield_branch ::
  "int \<Rightarrow> (int, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_managed_yield_branch y =
     condition
       (\<lambda>s. y = 1 \<or>
          Scheduler_V611_Parse.globals.xMissedYield_' s = 1)
       (do {
          modify
            (Scheduler_V611_Parse.globals.xMissedYield_'_update
              (\<lambda>_. 0));
          ret \<leftarrow>
            Scheduler_V611_Delay_Translation.eal6_port_yield';
          return 1
        })
       (return 0)"

lemma CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_missed_yieldD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "Scheduler_V611_Parse.globals.xMissedYield_' c =
       (if sa_missed_yield a then 1 else 0)"
proof -
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c (normalize_yield_count_abs a)
       managed termination external"
    using entry
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
  obtain c0 where overlay:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 (normalize_yield_count_abs a)
         managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF protected] .
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    full:
      "CursorGeneralStrongVTaskIncrementTickEntryRel
         D c0 (normalize_yield_count_abs a) managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF public] .
  have scalar:
    "scheduler_managed_scalar_rel c0
       (normalize_yield_count_abs a) managed"
    using full
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def
        CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have missed0:
    "Scheduler_V611_Parse.globals.xMissedYield_' c0 =
       (if sa_missed_yield (normalize_yield_count_abs a) then 1 else 0)"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
  show ?thesis
    using overlay missed0
    by (simp add: normalize_yield_count_abs_def scheduler_port_overlay_def)
qed

theorem CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield_branch:
  fixes y :: int
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "resume_managed_yield_branch y \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result
         (if resume_managed_yield_requested y a
          then (1 :: int) else 0) \<and>
       t = (if resume_managed_yield_requested y a
            then p2_yield_state (resume_clear_missed_yield_state c)
            else c) \<and>
       YieldAbs
         (resume_managed_yield_requested y a)
         (resume_managed_yield_caller_abs y a)
         (resume_managed_yield_requested y a)
         (resume_managed_yield_final_abs y a) \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D depth irq_mask t
         (resume_managed_yield_final_abs y a)
         managed termination external\<rbrace>"
proof -
  let ?requested = "resume_managed_yield_requested y a"
  have missed:
    "Scheduler_V611_Parse.globals.xMissedYield_' c =
       (if sa_missed_yield a then 1 else 0)"
    by (rule
      CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_missed_yieldD[
        OF entry])
  have guard_eq:
    "(y = 1 \<or>
       Scheduler_V611_Parse.globals.xMissedYield_' c = 1) = ?requested"
    using missed
    by (auto simp: resume_managed_yield_requested_def)
  show ?thesis
  proof (cases ?requested)
    case True
    have guard_true:
      "y = 1 \<or>
       Scheduler_V611_Parse.globals.xMissedYield_' c = 1"
      using guard_eq True by simp
    have cleared:
      "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D depth irq_mask (resume_clear_missed_yield_state c)
         (a\<lparr>sa_missed_yield := False\<rparr>)
         managed termination external"
      by (rule
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_clear_missed_yieldI[
          OF entry])
    note clear_source =
      CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_clear_missed_yield[
        OF entry]
    note yield_source =
      CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield[
        OF cleared]
    have true_block:
      "(do {
          modify
            (Scheduler_V611_Parse.globals.xMissedYield_'_update
              (\<lambda>_. 0));
          ret \<leftarrow>
            Scheduler_V611_Delay_Translation.eal6_port_yield';
          return 1
        }) \<bullet> c
       \<lbrace>\<lambda>r t.
         r = Result (1 :: int) \<and>
         t = p2_yield_state (resume_clear_missed_yield_state c) \<and>
         CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
           D depth irq_mask t
           (request_yield
             (a\<lparr>sa_missed_yield := False\<rparr>))
           managed termination external\<rbrace>"
    proof -
      show ?thesis
        apply (rule runs_to_bind)
        apply (rule runs_to_weaken[OF clear_source])
         apply clarsimp
        apply (rule runs_to_bind)
        apply (rule runs_to_weaken[OF yield_source])
        by clarsimp
    qed
    show ?thesis
      unfolding resume_managed_yield_branch_def
      apply (simp only: runs_to_condition_iff)
      apply (simp only: guard_true if_True)
      apply (rule runs_to_weaken[OF true_block])
      using True
      by (simp add: resume_managed_yield_caller_abs_def
          resume_managed_yield_final_abs_def YieldAbs_def)
  next
    case False
    have guard_false:
      "\<not> (y = 1 \<or>
        Scheduler_V611_Parse.globals.xMissedYield_' c = 1)"
      using guard_eq False by simp
    have requested_false:
      "\<not> resume_managed_yield_requested y a"
      using False .
    have caller_eq:
      "resume_managed_yield_caller_abs y a = a"
      using requested_false
      by (simp add: resume_managed_yield_caller_abs_def)
    have final_eq:
      "resume_managed_yield_final_abs y a = a"
      using requested_false caller_eq
      by (simp add: resume_managed_yield_final_abs_def)
    show ?thesis
      unfolding resume_managed_yield_branch_def
      apply (simp only: runs_to_condition_iff)
      apply (simp only: guard_false if_False)
      apply runs_to_vcg
      apply (rule requested_false)
      apply (simp add: caller_eq final_eq)
      using entry final_eq
      by simp
  qed
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

  val _ = audit_exact "proof-port yield-count selector" 0
    @{thm p2_yield_state_yield_count}
  val _ = audit_exact "proof-port yield commutes with overlay" 0
    @{thm p2_yield_state_port_overlay}
  val _ = audit_exact "core wf frames yield-count update" 0
    @{thm core_wf_yield_count_update}
  val _ = audit_exact "cursor canonicalization frames yield-count update" 0
    @{thm canonicalize_scheduler_cursors_yield_count_update}
  val _ = audit_exact "cursor-general core frames yield-count update" 0
    @{thm cursor_general_core_wf_yield_count_update}
  val _ = audit_exact "current relation frames proof-port yield" 0
    @{thm scheduler_current_rel_p2_yield_state}
  val _ = audit_exact "managed proof-port yield exact source" 0
    @{thm resume_managed_eal6_port_yield_exact}
  val _ = audit_exact "snapshot proof-port yield" 1
    @{thm CursorGeneralStrongSchedulerSnapshotRel_p2_yield_stateI}
  val _ = audit_exact "protected entry proof-port yield" 1
    @{thm CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_p2_yield_stateI}
  val _ = audit_exact "staged normalized request-yield step" 1
    @{thm normalize_yield_count_abs_request_yield_step}
  val _ = audit_exact "modular protected entry proof-port yield" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_p2_yield_stateI}
  val _ = audit_exact "generated modular proof-port yield" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield}
  val _ = audit_exact "modular protected entry missed-yield observation" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_missed_yieldD}
  val _ = audit_exact "generated modular guarded yield branch" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield_branch}
\<close>

end
