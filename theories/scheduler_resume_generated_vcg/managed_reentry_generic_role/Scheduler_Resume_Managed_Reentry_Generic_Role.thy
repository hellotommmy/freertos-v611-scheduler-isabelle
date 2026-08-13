theory Scheduler_Resume_Managed_Reentry_Generic_Role
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Domain_Wake.Scheduler_Resume_Managed_Reentry_Domain_Wake"
begin

lemma resume_pending_drained_generic_role_match:
  assumes pure: "resume_pending_entry_rel C P"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
    and old: "rps_generic_family P g = q"
    and target_ne:
      "g \<noteq> rpc_ready_root C (rpc_priority C t)"
  shows
    "rps_generic_family (resume_pending_drained_snapshot C t P) g =
       list_remove_abs (Generic t) q"
proof -
  have ne:
    "rpc_generic_owner C t \<noteq>
       rpc_ready_root C (rpc_priority C t)"
    using resume_pending_entry_head_facts[OF pure tasks] by blast
  show ?thesis
  proof (cases "g = rpc_generic_owner C t")
    case True
    show ?thesis
      using resume_pending_drained_generic_at[OF ne, of P g]
        target_ne True old
      by simp
  next
    case False
    have fresh:
      "Generic t \<notin> set (ring (rps_generic_family P g))"
      using resume_pending_entry_uniqueD[OF pure tasks root] False
      by simp
    have wf: "xlist_wf (rps_generic_family P g)"
      by (rule resume_pending_entry_wf_atD[OF pure root])
    have identity:
      "list_remove_abs (Generic t) (rps_generic_family P g) =
         rps_generic_family P g"
      by (rule list_remove_abs_nonmember[OF wf fresh])
    show ?thesis
      using resume_pending_drained_generic_at[OF ne, of P g]
        target_ne False old identity
      by simp
  qed
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_generic_roleD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "strong_generic_role_projection
       (resume_one_pending_abs t a) termination
       (rps_generic_family (resume_pending_drained_snapshot C t P))"
proof -
  let ?after = "resume_one_pending_abs t a"
  let ?PR = "resume_pending_drained_snapshot C t P"
  let ?ready =
    "\<lambda>p. abi_list_ptr (sr_ready generated_scheduler_roots p)"
  let ?da =
    "abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
  let ?db =
    "abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
  let ?susp =
    "abi_list_ptr (sr_suspended generated_scheduler_roots)"
  let ?term =
    "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"

  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c0 a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have role0:
    "strong_generic_role_projection a termination generic_abs"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have roots_eq: "rpc_generic_roots C = GenericRootUniverse"
    and ready_root_eq:
      "rpc_ready_root C =
         (\<lambda>p. abi_list_ptr (sr_ready generated_scheduler_roots p))"
    and priority_eq: "rpc_priority C = sa_priority a"
    and family_eq: "rps_generic_family P = generic_abs"
    using alignment
    by (simp_all add: resume_pending_managed_phase_alignment_def)
  have role:
    "strong_generic_role_projection a termination (rps_generic_family P)"
    using role0 family_eq by simp
  note head = resume_pending_entry_head_facts[OF pure tasks]
  have priority_bound_C: "rpc_priority C t < 4"
    using head by blast
  have priority_bound: "sa_priority a t < 4"
    using priority_bound_C priority_eq by simp
  have owner_target_ne:
    "rpc_generic_owner C t \<noteq>
       rpc_ready_root C (rpc_priority C t)"
    using head by blast
  have target_eq:
    "rpc_ready_root C (rpc_priority C t) =
       ?ready (sa_priority a t)"
    using ready_root_eq priority_eq by simp
  have owner_eq:
    "rpc_generic_owner C t = resume_pending_managed_owner a t"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_head_owner_eq[
        OF phase tasks])
  have captured:
    "pending_generic_key_abs t a = rpc_K_G C t"
    using
      CursorGeneralStrongResumePendingManagedPhaseRel_captured_keyD[
        OF phase tasks]
    by blast

  have ready_target_iff:
    "\<And>p. p < 4 \<Longrightarrow>
       (?ready p = rpc_ready_root C (rpc_priority C t)) \<longleftrightarrow>
         p = sa_priority a t"
  proof -
    fix p :: nat
    assume bound: "p < 4"
    show
      "(?ready p = rpc_ready_root C (rpc_priority C t)) \<longleftrightarrow>
         p = sa_priority a t"
    proof
      assume equal:
        "?ready p = rpc_ready_root C (rpc_priority C t)"
      have roots_equal:
        "?ready p = ?ready (sa_priority a t)"
        using equal target_eq by simp
      show "p = sa_priority a t"
        by (rule generated_ready_raw_root_inj[
              OF bound priority_bound roots_equal])
    next
      assume "p = sa_priority a t"
      then show "?ready p = rpc_ready_root C (rpc_priority C t)"
        using target_eq by simp
    qed
  qed
  have ready_owner_ne:
    "\<And>p. p < 4 \<Longrightarrow> ?ready p \<noteq> rpc_generic_owner C t"
  proof -
    fix p :: nat
    assume bound: "p < 4"
    show "?ready p \<noteq> rpc_generic_owner C t"
      using owner_eq
        generated_ready_raw_root_neq_delayed_a[OF bound]
        generated_ready_raw_root_neq_delayed_b[OF bound]
        generated_ready_raw_root_neq_suspended[OF bound]
      by (auto simp: resume_pending_managed_owner_def
          split: if_splits)
  qed

  have ready_match:
    "\<And>p. p < 4 \<Longrightarrow>
       rps_generic_family ?PR (?ready p) = sa_ready ?after p"
  proof -
    fix p :: nat
    assume bound: "p < 4"
    have before:
      "rps_generic_family P (?ready p) = sa_ready a p"
      using role bound
      by (simp add: strong_generic_role_projection_def)
    have owner_ne:
      "?ready p \<noteq> rpc_generic_owner C t"
      by (rule ready_owner_ne[OF bound])
    show
      "rps_generic_family ?PR (?ready p) = sa_ready ?after p"
    proof (cases "p = sa_priority a t")
      case True
      have at_target:
        "?ready p = rpc_ready_root C (rpc_priority C t)"
        using ready_target_iff[OF bound] True by simp
      have post:
        "rps_generic_family ?PR (?ready p) =
           list_insert_end_abs (Generic t) (rpc_K_G C t)
             (rps_generic_family P (?ready p))"
        using resume_pending_drained_generic_at[
          OF owner_target_ne, of P "?ready p"] at_target
        by simp
      show ?thesis
        using post before captured True
        by (simp add: resume_one_pending_abs_def
            resume_remove_generic_abs_def
            resume_add_ready_with_key_abs_def Let_def)
    next
      case False
      have not_target:
        "?ready p \<noteq> rpc_ready_root C (rpc_priority C t)"
        using ready_target_iff[OF bound] False by simp
      have post:
        "rps_generic_family ?PR (?ready p) =
           rps_generic_family P (?ready p)"
        using resume_pending_drained_generic_at[
          OF owner_target_ne, of P "?ready p"]
          not_target owner_ne
        by simp
      show ?thesis
        using post before False
        by (simp add: resume_one_pending_abs_def
            resume_remove_generic_abs_def
            resume_add_ready_with_key_abs_def Let_def)
    qed
  qed

  have da_universe: "?da \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_delayed_aI)
  have db_universe: "?db \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_delayed_bI)
  have susp_universe: "?susp \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_suspendedI)
  have da_root: "?da \<in> rpc_generic_roots C"
    and db_root: "?db \<in> rpc_generic_roots C"
    and susp_root: "?susp \<in> rpc_generic_roots C"
    using roots_eq da_universe db_universe susp_universe by simp_all
  have da_before: "rps_generic_family P ?da = sa_delayed_a a"
    and db_before: "rps_generic_family P ?db = sa_delayed_b a"
    and susp_before: "rps_generic_family P ?susp = sa_suspended a"
    and term_before: "rps_generic_family P ?term = termination"
    using role
    by (simp_all add: strong_generic_role_projection_def)
  have da_target_ne:
    "?da \<noteq> rpc_ready_root C (rpc_priority C t)"
  proof
    assume equal:
      "?da = rpc_ready_root C (rpc_priority C t)"
    have "?ready (sa_priority a t) = ?da"
      using target_eq equal by simp
    then show False
      using generated_ready_raw_root_neq_delayed_a[OF priority_bound]
      by blast
  qed
  have target_db_ne:
    "rpc_ready_root C (rpc_priority C t) \<noteq> ?db"
    using target_eq
      generated_ready_raw_root_neq_delayed_b[OF priority_bound]
    by simp
  have db_target_ne:
    "?db \<noteq> rpc_ready_root C (rpc_priority C t)"
    using target_db_ne by (rule not_sym)
  have target_susp_ne:
    "rpc_ready_root C (rpc_priority C t) \<noteq> ?susp"
    using target_eq
      generated_ready_raw_root_neq_suspended[OF priority_bound]
    by simp
  have susp_target_ne:
    "?susp \<noteq> rpc_ready_root C (rpc_priority C t)"
    using target_susp_ne by (rule not_sym)
  have target_term_ne:
    "rpc_ready_root C (rpc_priority C t) \<noteq> ?term"
    using target_eq
      generated_ready_raw_root_neq_termination[OF priority_bound]
    by simp
  have term_target_ne:
    "?term \<noteq> rpc_ready_root C (rpc_priority C t)"
    using target_term_ne by (rule not_sym)

  have da_post:
    "rps_generic_family ?PR ?da =
       list_remove_abs (Generic t) (sa_delayed_a a)"
    by (rule resume_pending_drained_generic_role_match[
          OF pure tasks da_root da_before da_target_ne])
  have db_post:
    "rps_generic_family ?PR ?db =
       list_remove_abs (Generic t) (sa_delayed_b a)"
    by (rule resume_pending_drained_generic_role_match[
          OF pure tasks db_root db_before db_target_ne])
  have susp_post:
    "rps_generic_family ?PR ?susp =
       list_remove_abs (Generic t) (sa_suspended a)"
    by (rule resume_pending_drained_generic_role_match[
          OF pure tasks susp_root susp_before susp_target_ne])
  have da_match:
    "rps_generic_family ?PR ?da = sa_delayed_a ?after"
    using da_post
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have db_match:
    "rps_generic_family ?PR ?db = sa_delayed_b ?after"
    using db_post
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have susp_match:
    "rps_generic_family ?PR ?susp = sa_suspended ?after"
    using susp_post
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)

  have owner_term_ne:
    "rpc_generic_owner C t \<noteq> ?term"
    using owner_eq generated_nonready_raw_roots_distinct
    by (auto simp: resume_pending_managed_owner_def
        split: if_splits)
  have term_owner_ne:
    "?term \<noteq> rpc_generic_owner C t"
    using owner_term_ne by (rule not_sym)
  have term_match:
    "rps_generic_family ?PR ?term = termination"
    using resume_pending_drained_generic_at[
      OF owner_target_ne, of P ?term]
      term_target_ne term_owner_ne term_before
    by simp

  show ?thesis
    unfolding strong_generic_role_projection_def
    using ready_match da_match db_match susp_match term_match
    by blast
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString actual)
    in () end

  val _ = audit_exact "drained Generic role match" 5
    @{thm resume_pending_drained_generic_role_match}
  val _ = audit_exact "managed reentry Generic role" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_generic_roleD}
\<close>

end
