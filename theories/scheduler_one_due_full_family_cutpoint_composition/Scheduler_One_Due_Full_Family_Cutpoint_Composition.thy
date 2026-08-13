theory Scheduler_One_Due_Full_Family_Cutpoint_Composition
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Family_Coverage_Remove_Preserved.Scheduler_Generic_Root_Family_Coverage_Remove_Preserved"
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Remove_Frames_Event_Coverage.Scheduler_Generic_Remove_Frames_Event_Coverage"
    "EAL6_FreeRTOS_V611_Scheduler_Event_Remove_Frames_Generic_Coverage.Scheduler_Event_Remove_Frames_Generic_Coverage"
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Coverage_Insert_End.Scheduler_Generic_Root_Coverage_Insert_End"
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Insert_End_Frames_Event_Coverage.Scheduler_Generic_Insert_End_Frames_Event_Coverage"
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_GateH.Scheduler_One_Due_Task_Phases_Reentry_GateH"
begin

text \<open>
  Whole-family coverage at the four source-order heap cutpoints of one due
  wake iteration:

    h0 --Generic remove--> hg --optional Event remove--> he
       --Generic insert-end--> hi.

  The coverage domain is the allocated-and-observable managed TCB set, not
  the runnable-only odc_live set.  Thus xTasksWaitingTermination and every
  other represented Generic root remain in scope.  The local Gate-H relation
  is used only for the selected task/source/target and for the already-checked
  physical Event branch.  It is never equated with either complete root
  universe.

  No Event owner is supplied as a premise.  In the linked branch the local
  Gate-H container observation is framed through the Generic removal, then
  complete Event coverage recovers the unique arbitrary external owner.  In
  the NULL branch complete Event coverage recovers global absence.  The final
  abstract families are definitionally the family components of the existing
  one_due_reentry_snapshot; they are not guessed poststates.
\<close>

definition one_due_generic_abs_after_remove ::
  "('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "one_due_generic_abs_after_remove C S =
     scheduler_family_remove_abs (ods_generic_family S)
       (odc_delayed_root C) (Generic (odc_task C))"

definition one_due_event_abs_after_remove ::
  "('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "one_due_event_abs_after_remove C branch S =
     (case branch of
        DueEventLinked owner \<Rightarrow>
          event_remove_abs_family (ods_event_family S) owner
            (odc_task C)
      | DueEventNull \<Rightarrow> ods_event_family S)"

definition one_due_generic_abs_after_insert ::
  "('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "one_due_generic_abs_after_insert C S =
     generic_family_insert_end_abs
       (one_due_generic_abs_after_remove C S)
       (one_due_target_root C) (odc_task C) (ods_generic_payload S)"

definition one_due_family_cross_storage ::
  "xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow> bool"
where
  "one_due_family_cross_storage external generic_raw event_raw \<longleftrightarrow>
     (\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (generic_raw g) \<inter>
           raw_xlist_storage e (event_raw e) = {})"

definition one_due_family_branch_witness ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> xLIST_C ptr one_due_event_branch \<Rightarrow> bool"
where
  "one_due_family_branch_witness D C hg event_raw external branch \<longleftrightarrow>
     (case branch of
        DueEventLinked owner \<Rightarrow>
          owner \<in> external \<and>
          event_item_raw_ptr D (odc_task C) \<in>
            set (ring (event_raw owner)) \<and>
          pvContainer_C
            (h_val hg (event_item_raw_ptr D (odc_task C))) =
              PTR_COERCE(xLIST_C \<rightarrow> unit) owner
      | DueEventNull \<Rightarrow>
          pvContainer_C
            (h_val hg (event_item_raw_ptr D (odc_task C))) = NULL \<and>
          raw_family_members (EventRootUniverse external) event_raw
            (event_item_raw_ptr D (odc_task C)) = {})"

definition one_due_full_family_cutpoints ::
  "xLIST_C ptr set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> 'tid set \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow> bool"
where
  "one_due_full_family_cutpoints
      external D managed C S h generic_raw event_raw branch \<longleftrightarrow>
     (let K_G = ods_generic_payload S;
          K_E = ods_event_payload S;
          p = generic_item_raw_ptr D (odc_task C);
          hg = one_due_generic_remove_heap D C h;
          generic_raw_g = one_due_generic_raw_after_remove D C generic_raw;
          generic_abs_g = one_due_generic_abs_after_remove C S;
          he = one_due_event_remove_heap D C branch hg;
          event_raw_e = one_due_event_raw_after_remove D C branch event_raw;
          event_abs_e = one_due_event_abs_after_remove C branch S;
          hi = one_due_ready_insert_heap D C generic_raw_g he;
          generic_raw_i = one_due_reentry_generic_raw D C he generic_raw;
          generic_abs_i = one_due_generic_abs_after_insert C S
      in
        GenericRootFamilyCoverage D h GenericRootUniverse
          generic_raw (ods_generic_family S) managed K_G \<and>
        EventRootFamilyCoverage external D h
          event_raw (ods_event_family S) managed K_E \<and>
        one_due_family_cross_storage external generic_raw event_raw \<and>

        GenericRootFamilyCoverage D hg GenericRootUniverse
          generic_raw_g generic_abs_g managed K_G \<and>
        EventRootFamilyCoverage external D hg
          event_raw (ods_event_family S) managed K_E \<and>
        one_due_family_cross_storage external generic_raw_g event_raw \<and>
        raw_family_members GenericRootUniverse generic_raw_g p = {} \<and>
        raw_fresh_for_insert (one_due_target_root C)
          (ring (generic_raw_g (one_due_target_root C))) p \<and>

        one_due_family_branch_witness D C hg event_raw external branch \<and>
        GenericRootFamilyCoverage D he GenericRootUniverse
          generic_raw_g generic_abs_g managed K_G \<and>
        EventRootFamilyCoverage external D he
          event_raw_e event_abs_e managed K_E \<and>
        one_due_family_cross_storage external generic_raw_g event_raw_e \<and>
        pvContainer_C
          (h_val he (event_item_raw_ptr D (odc_task C))) = NULL \<and>
        raw_family_members (EventRootUniverse external) event_raw_e
          (event_item_raw_ptr D (odc_task C)) = {} \<and>

        GenericRootFamilyCoverage D hi GenericRootUniverse
          generic_raw_i generic_abs_i managed K_G \<and>
        EventRootFamilyCoverage external D hi
          event_raw_e event_abs_e managed K_E \<and>
        one_due_family_cross_storage external generic_raw_i event_raw_e \<and>

        generic_abs_i =
          ods_generic_family (one_due_reentry_snapshot C branch S) \<and>
        event_abs_e =
          ods_event_family (one_due_reentry_snapshot C branch S))"

lemma one_due_generic_raw_after_remove_is_family_remove:
  "one_due_generic_raw_after_remove D C generic_raw =
     scheduler_family_remove_raw generic_raw (odc_delayed_root C)
       (generic_item_raw_ptr D (odc_task C))"
  by (rule ext)
     (simp add: one_due_generic_raw_after_remove_def
       scheduler_family_remove_raw_def one_due_generic_raw_ptr_def
       generic_item_raw_ptr_def)

lemma one_due_generic_abs_after_insert_is_reentry:
  "one_due_generic_abs_after_insert C S =
     ods_generic_family (one_due_reentry_snapshot C branch S)"
  by (rule ext)
     (simp add: one_due_generic_abs_after_insert_def
       one_due_generic_abs_after_remove_def generic_family_insert_end_abs_def
       scheduler_family_remove_abs_def one_due_reentry_snapshot_generic_at
       Let_def)

lemma one_due_event_abs_after_remove_is_reentry:
  "one_due_event_abs_after_remove C branch S =
     ods_event_family (one_due_reentry_snapshot C branch S)"
  by (rule ext)
     (cases branch;
      simp add: one_due_event_abs_after_remove_def
        event_remove_abs_family_def one_due_reentry_snapshot_event_at)

lemma one_due_cross_storageI:
  assumes generic:
      "GenericRootFamilyCoverage D h GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and event:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
  shows "one_due_family_cross_storage external generic_raw event_raw"
  using GenericEventRootFamilyCoverage_cross_storage_all[OF generic event]
  by (simp add: one_due_family_cross_storage_def)

theorem one_due_full_family_cutpoint_composition:
  assumes local:
      "one_due_gateH_entry_rel D R c current C branch S
         generic_raw event_raw"
    and live_subset: "odc_live C \<subseteq> managed"
    and generic_coverage:
      "GenericRootFamilyCoverage D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         GenericRootUniverse generic_raw (ods_generic_family S)
         managed (ods_generic_payload S)"
    and event_coverage:
      "EventRootFamilyCoverage external D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         event_raw (ods_event_family S) managed (ods_event_payload S)"
    and source_global: "odc_delayed_root C \<in> GenericRootUniverse"
    and target_global: "one_due_target_root C \<in> GenericRootUniverse"
    and pending_empty:
      "ring (ods_event_family S GeneratedPendingEventRoot) = []"
  shows
    "one_due_full_family_cutpoints external D managed C S
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       generic_raw event_raw branch"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?t = "odc_task C"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?p = "generic_item_raw_ptr D ?t"
  let ?ep = "event_item_raw_ptr D ?t"
  let ?hg = "one_due_generic_remove_heap D C ?h"
  let ?generic_raw_g =
    "one_due_generic_raw_after_remove D C generic_raw"
  let ?generic_abs_g = "one_due_generic_abs_after_remove C S"

  have task_live: "?t \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have task: "?t \<in> managed"
    by (rule subsetD[OF live_subset task_live])
  have raw_member_local:
      "one_due_generic_raw_ptr D ?t \<in>
         set (ring (generic_raw ?source))"
    by (rule one_due_gateH_source_memberD[OF local])
  have raw_member:
      "?p \<in> set (ring (generic_raw ?source))"
    using raw_member_local
    by (simp add: one_due_generic_raw_ptr_def generic_item_raw_ptr_def)

  have generic_hg:
      "GenericRootFamilyCoverage D ?hg GenericRootUniverse
         ?generic_raw_g ?generic_abs_g managed
         (ods_generic_payload S)"
  proof -
    have post:
      "GenericRootFamilyCoverage D (raw_remove_concrete_heap ?h ?p)
         GenericRootUniverse
         (scheduler_family_remove_raw generic_raw ?source ?p)
         (scheduler_family_remove_abs (ods_generic_family S) ?source
           (Generic ?t)) managed (ods_generic_payload S)"
      by (rule GenericRootFamilyCoverage_remove_preserved[
            OF generic_coverage source_global task raw_member])
    show ?thesis
      using post
      by (simp add: one_due_generic_remove_heap_def
          one_due_generic_raw_after_remove_is_family_remove
          one_due_generic_abs_after_remove_def one_due_generic_raw_ptr_def
          generic_item_raw_ptr_def)
  qed
  have event_hg:
      "EventRootFamilyCoverage external D ?hg
         event_raw (ods_event_family S) managed (ods_event_payload S)"
  proof -
    have post:
      "EventRootFamilyCoverage external D (raw_remove_concrete_heap ?h ?p)
         event_raw (ods_event_family S) managed (ods_event_payload S)"
      by (rule Generic_remove_frames_Event_coverage[
            OF generic_coverage event_coverage source_global task raw_member])
    show ?thesis
      using post
      by (simp add: one_due_generic_remove_heap_def
          one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
  qed
  have cross_h:
      "one_due_family_cross_storage external generic_raw event_raw"
    by (rule one_due_cross_storageI[OF generic_coverage event_coverage])
  have cross_hg:
      "one_due_family_cross_storage external ?generic_raw_g event_raw"
    by (rule one_due_cross_storageI[OF generic_hg event_hg])

  have generic_pre:
      "scheduler_family_pre_rel ?h GenericRootUniverse generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_coverage])
  have remove_pre_unlinked:
      "scheduler_family_pre_rel (raw_remove_concrete_heap ?h ?p)
          GenericRootUniverse
          (scheduler_family_remove_raw generic_raw ?source ?p) managed D \<and>
       raw_family_globally_unlinked (raw_remove_concrete_heap ?h ?p)
          GenericRootUniverse
          (scheduler_family_remove_raw generic_raw ?source ?p) ?p"
    by (rule scheduler_family_remove_pre_rel_and_unlinked[
          OF generic_pre source_global raw_member])
  have generic_absent:
      "raw_family_members GenericRootUniverse ?generic_raw_g ?p = {}"
    using remove_pre_unlinked
    by (simp add: raw_family_globally_unlinked_def
        one_due_generic_raw_after_remove_is_family_remove)
  have source_target_distinct: "?source \<noteq> ?target"
    using one_due_gateH_pure_entryD[OF local]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have local_fresh:
      "raw_fresh_for_insert ?target (ring (generic_raw ?target))
         (one_due_generic_raw_ptr D ?t)"
    by (rule one_due_gateH_generic_target_freshD[OF local])
  have fresh:
      "raw_fresh_for_insert ?target (ring (?generic_raw_g ?target)) ?p"
    using local_fresh source_target_distinct
    by (simp add: one_due_generic_raw_after_remove_def
        one_due_generic_raw_ptr_def generic_item_raw_ptr_def)

  show ?thesis
  proof (cases branch)
    case DueEventNull
    have local_null:
        "one_due_gateH_entry_rel D R c current C DueEventNull S
           generic_raw event_raw"
      using local DueEventNull by simp
    have event_null_hg:
        "pvContainer_C (h_val ?hg ?ep) = NULL"
      by (rule one_due_gateH_null_event_after_genericD[OF local_null])
    have event_absent_hg:
        "raw_family_members (EventRootUniverse external) event_raw ?ep = {}"
      using EventRootFamilyCoverage_null_iff_global_absence[
        OF event_hg task] event_null_hg by blast
    have branch_witness:
        "one_due_family_branch_witness D C ?hg event_raw external
           DueEventNull"
      using event_null_hg event_absent_hg
      by (simp add: one_due_family_branch_witness_def)

    let ?branch = "DueEventNull"
    let ?he = "one_due_event_remove_heap D C ?branch ?hg"
    let ?event_raw_e =
      "one_due_event_raw_after_remove D C ?branch event_raw"
    let ?event_abs_e = "one_due_event_abs_after_remove C ?branch S"
    let ?hi = "one_due_ready_insert_heap D C ?generic_raw_g ?he"
    let ?generic_raw_i =
      "one_due_reentry_generic_raw D C ?he generic_raw"
    let ?generic_abs_i = "one_due_generic_abs_after_insert C S"

    have generic_he:
        "GenericRootFamilyCoverage D ?he GenericRootUniverse
           ?generic_raw_g ?generic_abs_g managed (ods_generic_payload S)"
      using generic_hg by (simp add: one_due_event_remove_heap_def)
    have event_he:
        "EventRootFamilyCoverage external D ?he ?event_raw_e ?event_abs_e
           managed (ods_event_payload S)"
      using event_hg
      by (simp add: one_due_event_remove_heap_def
          one_due_event_raw_after_remove_def
          one_due_event_abs_after_remove_def)
    have cross_he:
        "one_due_family_cross_storage external ?generic_raw_g ?event_raw_e"
      by (rule one_due_cross_storageI[OF generic_he event_he])
    have event_null_he:
        "pvContainer_C (h_val ?he ?ep) = NULL"
      using event_null_hg by (simp add: one_due_event_remove_heap_def)
    have event_absent_he:
        "raw_family_members (EventRootUniverse external) ?event_raw_e ?ep = {}"
      using event_absent_hg
      by (simp add: one_due_event_raw_after_remove_def)

    have generic_hi:
        "GenericRootFamilyCoverage D ?hi GenericRootUniverse
           ?generic_raw_i ?generic_abs_i managed (ods_generic_payload S)"
    proof -
      have post:
          "GenericRootFamilyCoverage D
             (raw_insert_concrete_heap ?he ?target
               (?generic_raw_g ?target) ?p)
             GenericRootUniverse
             (scheduler_family_insert_end_raw ?he ?generic_raw_g ?target ?p)
             (generic_family_insert_end_abs ?generic_abs_g ?target ?t
               (ods_generic_payload S)) managed (ods_generic_payload S)"
        by (rule GenericRootFamilyCoverage_insert_end_preserved[
              OF generic_he target_global task generic_absent fresh])
      show ?thesis
        using post
        by (simp add: one_due_ready_insert_heap_def
            one_due_reentry_generic_raw_def
            one_due_generic_abs_after_insert_def
            one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
    qed
    have event_hi:
        "EventRootFamilyCoverage external D ?hi ?event_raw_e ?event_abs_e
           managed (ods_event_payload S)"
    proof -
      have post:
          "EventRootFamilyCoverage external D
             (raw_insert_concrete_heap ?he ?target
               (?generic_raw_g ?target) ?p)
             ?event_raw_e ?event_abs_e managed (ods_event_payload S)"
        by (rule Generic_insert_end_frames_Event_coverage[
              OF generic_he event_he target_global task fresh])
      show ?thesis
        using post
        by (simp add: one_due_ready_insert_heap_def
            one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
    qed
    have cross_hi:
        "one_due_family_cross_storage external ?generic_raw_i ?event_raw_e"
      by (rule one_due_cross_storageI[OF generic_hi event_hi])
    have generic_snapshot:
        "?generic_abs_i =
           ods_generic_family (one_due_reentry_snapshot C ?branch S)"
      by (rule one_due_generic_abs_after_insert_is_reentry)
    have event_snapshot:
        "?event_abs_e =
           ods_event_family (one_due_reentry_snapshot C ?branch S)"
      by (rule one_due_event_abs_after_remove_is_reentry)
    show ?thesis
      using DueEventNull generic_coverage event_coverage cross_h generic_hg
        event_hg cross_hg generic_absent fresh branch_witness generic_he
        event_he cross_he event_null_he event_absent_he generic_hi event_hi
        cross_hi generic_snapshot event_snapshot
      by (simp add: one_due_full_family_cutpoints_def Let_def)
  next
    case (DueEventLinked owner)
    have local_linked:
        "one_due_gateH_entry_rel D R c current C (DueEventLinked owner) S
           generic_raw event_raw"
      using local DueEventLinked by simp
    note local_branch = one_due_gateH_event_branchD[OF local_linked]
    have owner_local_root: "owner \<in> odc_event_roots C"
      using local_branch by (auto simp: one_due_external_roots_def)
    have container_h:
        "pvContainer_C (h_val ?h ?ep) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
      using local_branch by simp
    have event_item_frame:
        "h_val ?hg ?ep = h_val ?h ?ep"
      by (rule one_due_gateH_generic_remove_event_item_frameD[
            OF local_linked task_live])
    have container_hg:
        "pvContainer_C (h_val ?hg ?ep) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
      using container_h event_item_frame by simp
    have owner_rel: "raw_xlist_rel ?h owner (event_raw owner)"
      by (rule scheduler_event_root_family_raw_rootD[
            OF one_due_gateH_event_relD[OF local_linked] owner_local_root])
    have owner_guard: "c_guard owner"
      using owner_rel
      by (auto simp: raw_xlist_rel_def raw_xlist_layout_def)
    have owner_nonnull:
        "PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<noteq> NULL"
      using c_guard_NULL[OF owner_guard] by simp
    have event_linked_hg:
        "pvContainer_C (h_val ?hg ?ep) \<noteq> NULL"
      using container_hg owner_nonnull by simp

    have linked_owner:
        "\<exists>global_owner. global_owner \<in> external \<and>
           ?ep \<in> set (ring (event_raw global_owner)) \<and>
           pvContainer_C (h_val ?hg ?ep) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) global_owner"
      by (rule EventRootFamilyCoverage_linked_owner_externalD[
            OF event_hg task pending_empty event_linked_hg])
    obtain global_owner where global_owner_external:
        "global_owner \<in> external"
      and global_member:
        "?ep \<in> set (ring (event_raw global_owner))"
      and global_container:
        "pvContainer_C (h_val ?hg ?ep) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) global_owner"
      using linked_owner by blast
    have coerced_owner:
        "PTR_COERCE(xLIST_C \<rightarrow> unit) owner =
         PTR_COERCE(xLIST_C \<rightarrow> unit) global_owner"
      using container_hg global_container by simp
    have owner_eq: "owner = global_owner"
      using coerced_owner by (simp only: ptr_coerce_eq)
    have owner_external: "owner \<in> external"
      using global_owner_external owner_eq by simp
    have event_member: "?ep \<in> set (ring (event_raw owner))"
      using global_member owner_eq by simp
    have owner_root: "owner \<in> EventRootUniverse external"
      by (rule EventRootUniverse_externalI[OF owner_external])
    have branch_witness:
        "one_due_family_branch_witness D C ?hg event_raw external
           (DueEventLinked owner)"
      using owner_external event_member container_hg
      by (simp add: one_due_family_branch_witness_def)

    let ?branch = "DueEventLinked owner"
    let ?he = "one_due_event_remove_heap D C ?branch ?hg"
    let ?event_raw_e =
      "one_due_event_raw_after_remove D C ?branch event_raw"
    let ?event_abs_e = "one_due_event_abs_after_remove C ?branch S"
    let ?hi = "one_due_ready_insert_heap D C ?generic_raw_g ?he"
    let ?generic_raw_i =
      "one_due_reentry_generic_raw D C ?he generic_raw"
    let ?generic_abs_i = "one_due_generic_abs_after_insert C S"

    have old_event_rel:
        "scheduler_event_root_family_rel D ?hg
           (EventRootUniverse external) GeneratedPendingEventRoot
           event_raw (ods_event_family S) managed (ods_event_payload S)"
      by (rule EventRootFamilyCoverage_relD[OF event_hg])
    have event_post_rel:
        "scheduler_event_root_family_rel D
           (raw_remove_concrete_heap ?hg ?ep)
           (EventRootUniverse external) GeneratedPendingEventRoot
           (event_remove_raw_family event_raw owner ?ep)
           (event_remove_abs_family (ods_event_family S) owner ?t)
           managed (ods_event_payload S)"
      by (rule scheduler_event_root_family_remove_preserved[
            OF old_event_rel owner_root task event_member])
    have event_he_native:
        "EventRootFamilyCoverage external D
           (raw_remove_concrete_heap ?hg ?ep)
           (event_remove_raw_family event_raw owner ?ep)
           (event_remove_abs_family (ods_event_family S) owner ?t)
           managed (ods_event_payload S)"
      using EventRootFamilyCoverage_external_wfD[OF event_hg] event_post_rel
      by (simp add: EventRootFamilyCoverage_def)
    have generic_he_native:
        "GenericRootFamilyCoverage D (raw_remove_concrete_heap ?hg ?ep)
           GenericRootUniverse ?generic_raw_g ?generic_abs_g managed
           (ods_generic_payload S)"
      by (rule Event_remove_frames_Generic_coverage[
            OF generic_hg event_hg owner_root task event_member])
    have event_post_null:
        "pvContainer_C
           (h_val (raw_remove_concrete_heap ?hg ?ep) ?ep) = NULL"
      using scheduler_event_root_family_remove_item_effect[
        OF old_event_rel owner_root task event_member] by simp
    have event_post_absent:
        "raw_family_members (EventRootUniverse external)
           (event_remove_raw_family event_raw owner ?ep) ?ep = {}"
      by (rule scheduler_event_root_family_remove_members_empty[
            OF old_event_rel owner_root task event_member])

    have generic_he:
        "GenericRootFamilyCoverage D ?he GenericRootUniverse
           ?generic_raw_g ?generic_abs_g managed (ods_generic_payload S)"
      using generic_he_native
      by (simp add: one_due_event_remove_heap_def)
    have event_he:
        "EventRootFamilyCoverage external D ?he ?event_raw_e ?event_abs_e
           managed (ods_event_payload S)"
      using event_he_native
      by (simp add: one_due_event_remove_heap_def
          one_due_event_raw_after_remove_def
          one_due_event_abs_after_remove_def
          event_remove_raw_family_def)
    have cross_he:
        "one_due_family_cross_storage external ?generic_raw_g ?event_raw_e"
      by (rule one_due_cross_storageI[OF generic_he event_he])
    have event_null_he:
        "pvContainer_C (h_val ?he ?ep) = NULL"
      using event_post_null by (simp add: one_due_event_remove_heap_def)
    have event_absent_he:
        "raw_family_members (EventRootUniverse external) ?event_raw_e ?ep = {}"
      using event_post_absent
      by (simp add: one_due_event_raw_after_remove_def
          event_remove_raw_family_def)

    have generic_hi:
        "GenericRootFamilyCoverage D ?hi GenericRootUniverse
           ?generic_raw_i ?generic_abs_i managed (ods_generic_payload S)"
    proof -
      have post:
          "GenericRootFamilyCoverage D
             (raw_insert_concrete_heap ?he ?target
               (?generic_raw_g ?target) ?p)
             GenericRootUniverse
             (scheduler_family_insert_end_raw ?he ?generic_raw_g ?target ?p)
             (generic_family_insert_end_abs ?generic_abs_g ?target ?t
               (ods_generic_payload S)) managed (ods_generic_payload S)"
        by (rule GenericRootFamilyCoverage_insert_end_preserved[
              OF generic_he target_global task generic_absent fresh])
      show ?thesis
        using post
        by (simp add: one_due_ready_insert_heap_def
            one_due_reentry_generic_raw_def
            one_due_generic_abs_after_insert_def
            one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
    qed
    have event_hi:
        "EventRootFamilyCoverage external D ?hi ?event_raw_e ?event_abs_e
           managed (ods_event_payload S)"
    proof -
      have post:
          "EventRootFamilyCoverage external D
             (raw_insert_concrete_heap ?he ?target
               (?generic_raw_g ?target) ?p)
             ?event_raw_e ?event_abs_e managed (ods_event_payload S)"
        by (rule Generic_insert_end_frames_Event_coverage[
              OF generic_he event_he target_global task fresh])
      show ?thesis
        using post
        by (simp add: one_due_ready_insert_heap_def
            one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
    qed
    have cross_hi:
        "one_due_family_cross_storage external ?generic_raw_i ?event_raw_e"
      by (rule one_due_cross_storageI[OF generic_hi event_hi])
    have generic_snapshot:
        "?generic_abs_i =
           ods_generic_family (one_due_reentry_snapshot C ?branch S)"
      by (rule one_due_generic_abs_after_insert_is_reentry)
    have event_snapshot:
        "?event_abs_e =
           ods_event_family (one_due_reentry_snapshot C ?branch S)"
      by (rule one_due_event_abs_after_remove_is_reentry)
    show ?thesis
      using DueEventLinked generic_coverage event_coverage cross_h generic_hg
        event_hg cross_hg generic_absent fresh branch_witness generic_he
        event_he cross_he event_null_he event_absent_he generic_hi event_hi
        cross_hi generic_snapshot event_snapshot
      by (simp add: one_due_full_family_cutpoints_def Let_def)
  qed
qed

end
