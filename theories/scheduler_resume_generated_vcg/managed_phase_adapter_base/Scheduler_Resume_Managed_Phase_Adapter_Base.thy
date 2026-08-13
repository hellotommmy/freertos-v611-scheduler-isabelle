theory Scheduler_Resume_Managed_Phase_Adapter_Base
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Gate_Base.Scheduler_Resume_Managed_Gate_Base"
begin

text \<open>
  Proof-only objects for the managed pending-drain phase.  The context's live
  field denotes the total managed/decoder domain.  Its pending task list is
  reconstructed from the public pending Event ring and is separately required
  to lie in sa_live.  The owner function remains a ghost: after re-entry its
  values for already-processed tasks are irrelevant and need not be
  recomputed.
\<close>

definition resume_pending_managed_tasks ::
  "'tid scheduler_abs \<Rightarrow> 'tid list"
where
  "resume_pending_managed_tasks a =
     map node_owner (ring (sa_pending a))"

definition resume_pending_managed_owner ::
  "'tid scheduler_abs \<Rightarrow> 'tid \<Rightarrow> xLIST_C ptr"
where
  "resume_pending_managed_owner a t =
     (if Generic t \<in> set (ring (sa_delayed_a a))
      then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
      else if Generic t \<in> set (ring (sa_delayed_b a))
      then abi_list_ptr (sr_delayed_b generated_scheduler_roots)
      else abi_list_ptr (sr_suspended generated_scheduler_roots))"

definition resume_pending_managed_current_priority ::
  "'tid scheduler_abs \<Rightarrow> nat"
where
  "resume_pending_managed_current_priority a =
     (case sa_current a of
        None \<Rightarrow> 0
      | Some t \<Rightarrow> sa_priority a t)"

definition resume_pending_canonical_managed_context ::
  "'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context"
where
  "resume_pending_canonical_managed_context a managed external K_G K_E =
     \<lparr>rpc_live = managed,
      rpc_tasks = resume_pending_managed_tasks a,
      rpc_generic_roots = GenericRootUniverse,
      rpc_event_roots = EventRootUniverse external,
      rpc_pending_root = GeneratedPendingEventRoot,
      rpc_generic_owner = resume_pending_managed_owner a,
      rpc_ready_root =
        (\<lambda>p. abi_list_ptr (sr_ready generated_scheduler_roots p)),
      rpc_priority = sa_priority a,
      rpc_current_priority = resume_pending_managed_current_priority a,
      rpc_K_G = K_G,
      rpc_K_E = K_E,
      rpc_entry_top = sa_top_ready a\<rparr>"

definition resume_pending_snapshot_of_one_due ::
  "('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_snapshot"
where
  "resume_pending_snapshot_of_one_due S =
     \<lparr>rps_generic_family = ods_generic_family S,
      rps_event_family = ods_event_family S,
      rps_generic_payload = ods_generic_payload S,
      rps_event_payload = ods_event_payload S,
      rps_top = ods_top S,
      rps_local_yield = False\<rparr>"

definition resume_pending_managed_phase_alignment ::
  "'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_snapshot \<Rightarrow> bool"
where
  "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P \<longleftrightarrow>
     rpc_live C = managed \<and>
     rpc_tasks C = resume_pending_managed_tasks a \<and>
     rpc_generic_roots C = GenericRootUniverse \<and>
     rpc_event_roots C = EventRootUniverse external \<and>
     rpc_pending_root C = GeneratedPendingEventRoot \<and>
     rpc_ready_root C =
       (\<lambda>p. abi_list_ptr (sr_ready generated_scheduler_roots p)) \<and>
     rpc_priority C = sa_priority a \<and>
     rpc_current_priority C = resume_pending_managed_current_priority a \<and>
     rpc_K_G C = K_G \<and>
     rpc_K_E C = K_E \<and>
     rpc_entry_top C = sa_top_ready a \<and>
     rps_generic_family P = generic_abs \<and>
     rps_event_family P = event_abs \<and>
     rps_generic_payload P = K_G \<and>
     rps_event_payload P = K_E \<and>
     rps_top P = sa_top_ready a"

definition CursorGeneralStrongResumePendingManagedPhaseRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_snapshot \<Rightarrow> bool"
where
  "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P \<longleftrightarrow>
     CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     resume_pending_entry_rel C P \<and>
     set (rpc_tasks C) \<subseteq> sa_live a \<and>
     resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"

lemma event_node_list_owner_map:
  assumes event: "\<forall>n\<in>set xs. \<exists>t. n = Event t"
  shows "map Event (map node_owner xs) = xs"
  using event
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons n xs)
  obtain t where n: "n = Event t"
    using Cons.prems by auto
  have tail: "\<forall>n\<in>set xs. \<exists>t. n = Event t"
    using Cons.prems by auto
  show ?case using Cons.IH[OF tail] by (simp add: n)
qed

lemma event_node_list_owner_set:
  assumes event: "\<forall>n\<in>set xs. \<exists>t. n = Event t"
  shows "set (map node_owner xs) = {t. Event t \<in> set xs}"
  using event
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons n xs)
  obtain t where n: "n = Event t"
    using Cons.prems by auto
  have tail: "\<forall>n\<in>set xs. \<exists>t. n = Event t"
    using Cons.prems by auto
  show ?case using Cons.IH[OF tail] by (auto simp add: n)
qed

lemma event_node_list_owner_distinct:
  assumes event: "\<forall>n\<in>set xs. \<exists>t. n = Event t"
    and distinct: "distinct xs"
  shows "distinct (map node_owner xs)"
proof -
  have injective: "inj_on node_owner (set xs)"
  proof (rule inj_onI)
    fix x y
    assume x: "x \<in> set xs"
      and y: "y \<in> set xs"
      and owner: "node_owner x = node_owner y"
    obtain tx where x_event: "x = Event tx"
      using event x by blast
    obtain ty where y_event: "y = Event ty"
      using event y by blast
    show "x = y" using owner x_event y_event by simp
  qed
  show ?thesis using distinct injective by (simp add: distinct_map)
qed

lemma resume_pending_canonical_managed_context_components:
  "rpc_live
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       managed \<and>
   rpc_tasks
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       resume_pending_managed_tasks a \<and>
   rpc_generic_roots
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       GenericRootUniverse \<and>
   rpc_event_roots
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       EventRootUniverse external \<and>
   rpc_pending_root
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       GeneratedPendingEventRoot \<and>
   rpc_generic_owner
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       resume_pending_managed_owner a \<and>
   rpc_ready_root
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       (\<lambda>p. abi_list_ptr (sr_ready generated_scheduler_roots p)) \<and>
   rpc_priority
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       sa_priority a \<and>
   rpc_current_priority
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       resume_pending_managed_current_priority a \<and>
   rpc_K_G
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       K_G \<and>
   rpc_K_E
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       K_E \<and>
   rpc_entry_top
      (resume_pending_canonical_managed_context a managed external K_G K_E) =
       sa_top_ready a"
  by (simp add: resume_pending_canonical_managed_context_def)

lemma resume_pending_snapshot_of_one_due_components:
  "rps_generic_family (resume_pending_snapshot_of_one_due S) =
       ods_generic_family S \<and>
   rps_event_family (resume_pending_snapshot_of_one_due S) =
       ods_event_family S \<and>
   rps_generic_payload (resume_pending_snapshot_of_one_due S) =
       ods_generic_payload S \<and>
   rps_event_payload (resume_pending_snapshot_of_one_due S) =
       ods_event_payload S \<and>
   rps_top (resume_pending_snapshot_of_one_due S) = ods_top S \<and>
   \<not> rps_local_yield (resume_pending_snapshot_of_one_due S)"
  by (simp add: resume_pending_snapshot_of_one_due_def)

lemma resume_pending_canonical_managed_phase_alignment:
  assumes projection:
    "strong_one_due_snapshot_projection a generic_abs event_abs K_G K_E S"
  shows
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E
       (resume_pending_canonical_managed_context a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
  using projection
  by (simp add: resume_pending_managed_phase_alignment_def
      resume_pending_canonical_managed_context_def
      resume_pending_snapshot_of_one_due_def
      strong_one_due_snapshot_projection_def)

lemma CursorGeneralStrongResumePendingManagedGateRel_pending_event_ringD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "event_ring (sa_pending a)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have canonical_core: "core_wf (canonicalize_scheduler_cursors a)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        cursor_general_core_wf_def Let_def)
  show ?thesis
    using canonical_core
    by (simp add: core_wf_def role_wf_def event_ring_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_pending_xlist_wfD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "xlist_wf (sa_pending a)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have core: "cursor_general_core_wf a"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have shape: "ring_shape_wf a"
    by (rule cursor_general_core_wf_ring_shapeD[OF core])
  show ?thesis using shape by (simp add: ring_shape_wf_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "ring (sa_pending a) = map Event (resume_pending_managed_tasks a)"
proof -
  have event: "event_ring (sa_pending a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_pending_event_ringD[
        OF gate])
  have nodes:
    "\<forall>n\<in>set (ring (sa_pending a)). \<exists>t. n = Event t"
    using event by (simp add: event_ring_def)
  show ?thesis
    using event_node_list_owner_map[OF nodes]
    by (simp add: resume_pending_managed_tasks_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_setD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "set (resume_pending_managed_tasks a) =
       event_task_set (sa_pending a)"
proof -
  have event: "event_ring (sa_pending a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_pending_event_ringD[
        OF gate])
  have nodes:
    "\<forall>n\<in>set (ring (sa_pending a)). \<exists>t. n = Event t"
    using event by (simp add: event_ring_def)
  show ?thesis
    using event_node_list_owner_set[OF nodes]
    by (simp add: resume_pending_managed_tasks_def event_task_set_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_distinctD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "distinct (resume_pending_managed_tasks a)"
proof -
  have event: "event_ring (sa_pending a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_pending_event_ringD[
        OF gate])
  have nodes:
    "\<forall>n\<in>set (ring (sa_pending a)). \<exists>t. n = Event t"
    using event by (simp add: event_ring_def)
  have wf: "xlist_wf (sa_pending a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_pending_xlist_wfD[
        OF gate])
  have distinct: "distinct (ring (sa_pending a))"
    using wf by (simp add: xlist_wf_def)
  show ?thesis
    using event_node_list_owner_distinct[OF nodes distinct]
    by (simp add: resume_pending_managed_tasks_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_liveD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "set (resume_pending_managed_tasks a) \<subseteq> sa_live a"
  using
    CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_setD[OF gate]
    CursorGeneralStrongResumePendingManagedGateRel_pending_liveD[OF gate]
  by simp

lemma CursorGeneralStrongResumePendingManagedGateRel_canonical_alignmentD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E
       (resume_pending_canonical_managed_context a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have projection:
    "strong_one_due_snapshot_projection a generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    by (rule resume_pending_canonical_managed_phase_alignment[OF projection])
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRelI:
  assumes gate:
      "CursorGeneralStrongResumePendingManagedGateRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pure: "resume_pending_entry_rel C P"
    and tasks_live: "set (rpc_tasks C) \<subseteq> sa_live a"
    and alignment:
      "resume_pending_managed_phase_alignment
         a managed external generic_abs event_abs K_G K_E C P"
  shows
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  using gate pure tasks_live alignment
  by (simp add: CursorGeneralStrongResumePendingManagedPhaseRel_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRelD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     resume_pending_entry_rel C P \<and>
     set (rpc_tasks C) \<subseteq> sa_live a \<and>
     resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
  using phase
  by (simp add: CursorGeneralStrongResumePendingManagedPhaseRel_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_gateD:
  "CursorGeneralStrongResumePendingManagedPhaseRel
     D c a managed termination external
     generic_raw generic_abs event_raw event_abs K_G K_E S C P
   \<Longrightarrow>
   CursorGeneralStrongResumePendingManagedGateRel
     D c a managed termination external
     generic_raw generic_abs event_raw event_abs K_G K_E S"
  by (simp add: CursorGeneralStrongResumePendingManagedPhaseRel_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_pureD:
  "CursorGeneralStrongResumePendingManagedPhaseRel
     D c a managed termination external
     generic_raw generic_abs event_raw event_abs K_G K_E S C P
   \<Longrightarrow> resume_pending_entry_rel C P"
  by (simp add: CursorGeneralStrongResumePendingManagedPhaseRel_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_tasks_liveD:
  "CursorGeneralStrongResumePendingManagedPhaseRel
     D c a managed termination external
     generic_raw generic_abs event_raw event_abs K_G K_E S C P
   \<Longrightarrow> set (rpc_tasks C) \<subseteq> sa_live a"
  by (simp add: CursorGeneralStrongResumePendingManagedPhaseRel_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD:
  "CursorGeneralStrongResumePendingManagedPhaseRel
     D c a managed termination external
     generic_raw generic_abs event_raw event_abs K_G K_E S C P
   \<Longrightarrow>
   resume_pending_managed_phase_alignment
     a managed external generic_abs event_abs K_G K_E C P"
  by (simp add: CursorGeneralStrongResumePendingManagedPhaseRel_def)

ML \<open>
  fun audit_exact label expected th =
    let
      val hyps = Thm.hyps_of th
      val prems = Thm.prems_of th
      val _ =
        if null hyps then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if length prems = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString (length prems))
    in () end

  val _ = audit_exact "Event-list owner map" 1
    @{thm event_node_list_owner_map}
  val _ = audit_exact "Event-list owner set" 1
    @{thm event_node_list_owner_set}
  val _ = audit_exact "Event-list owner distinctness" 2
    @{thm event_node_list_owner_distinct}
  val _ = audit_exact "canonical managed pending context components" 0
    @{thm resume_pending_canonical_managed_context_components}
  val _ = audit_exact "one-due to pending snapshot components" 0
    @{thm resume_pending_snapshot_of_one_due_components}
  val _ = audit_exact "canonical managed phase alignment" 1
    @{thm resume_pending_canonical_managed_phase_alignment}
  val _ = audit_exact "managed gate pending Event ring" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_pending_event_ringD}
  val _ = audit_exact "managed gate pending xlist" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_pending_xlist_wfD}
  val _ = audit_exact "managed gate task-ring reconstruction" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD}
  val _ = audit_exact "managed gate task-set reconstruction" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_setD}
  val _ = audit_exact "managed gate task distinctness" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_distinctD}
  val _ = audit_exact "managed gate task live subset" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_liveD}
  val _ = audit_exact "managed gate canonical alignment" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_canonical_alignmentD}
  val _ = audit_exact "managed phase constructor" 4
    @{thm CursorGeneralStrongResumePendingManagedPhaseRelI}
  val _ = audit_exact "managed phase destructor" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRelD}
  val _ = audit_exact "managed phase gate projection" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_gateD}
  val _ = audit_exact "managed phase pure projection" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_pureD}
  val _ = audit_exact "managed phase task-live projection" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_tasks_liveD}
  val _ = audit_exact "managed phase alignment projection" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD}
\<close>

end
