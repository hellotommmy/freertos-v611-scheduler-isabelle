theory Scheduler_Unlocked_Tick_Pointer_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Managed_Entry_Assembler.Scheduler_Unlocked_Tick_Managed_Entry_Assembler"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Exact.Scheduler_Unlocked_Tick_Prefix_Source_Exact"
begin

text \<open>
  Physical delayed-head reads use the allocated-and-observable managed domain
  M.  In particular, none of the decoder facts below is restricted to the
  runnable domain sa_live.  The three source cases are symbolic list cases:
  a due head, a future head after an empty due prefix, and the empty ring.
\<close>

lemma unlocked_tick_current_generic_rootI:
  assumes role: "scheduler_role_rel generated_scheduler_roots c a"
  shows
    "abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)
       \<in> GenericRootUniverse"
proof -
  have delayed:
    "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
       (if sa_current_role_a a
        then sr_delayed_a generated_scheduler_roots
        else sr_delayed_b generated_scheduler_roots)"
    using role by (simp add: scheduler_role_rel_def)
  show ?thesis
  proof (cases "sa_current_role_a a")
    case True
    have current:
      "abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) =
       abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
      using delayed True by simp
    show ?thesis
      using GenericRootUniverse_delayed_aI
      by (simp only: current)
  next
    case False
    have current:
      "abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) =
       abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
      using delayed False by simp
    show ?thesis
      using GenericRootUniverse_delayed_bI
      by (simp only: current)
  qed
qed

lemma unlocked_tick_current_generic_projectionD:
  assumes role: "scheduler_role_rel generated_scheduler_roots c a"
    and projection:
      "strong_generic_role_projection a termination generic_abs"
  shows
    "generic_abs
       (abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)) =
       current_delayed_ring a"
  using role projection
  by (cases "sa_current_role_a a")
     (simp_all add: scheduler_role_rel_def
        strong_generic_role_projection_def current_delayed_ring_def)

lemma GenericRootFamilyCoverage_managed_view_decodeD:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       generic_raw generic_abs M K_G"
  shows "scheduler_decode_rel D (managed_scheduler_view a M)"
proof -
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse generic_raw M D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have geometry: "universal_tcb_geometry M D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have laws: "universal_decoder_laws M D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
  show ?thesis
  proof (rule universal_geometry_scheduler_decode_rel)
    show "universal_scheduler_geometry M D"
      using geometry laws
      by (simp add: universal_scheduler_geometry_def)
    show "sa_live (managed_scheduler_view a M) = M"
      by (simp add: managed_scheduler_view_def)
  qed
qed

lemma unlocked_tick_current_delayed_countD:
  assumes coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs M K_G"
    and role: "scheduler_role_rel generated_scheduler_roots c a"
    and projection:
      "strong_generic_role_projection a termination generic_abs"
  shows
    "unat (generated_current_delayed_count c) =
       length (ring (current_delayed_ring a))"
proof -
  let ?lp =
    "abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
  have root: "?lp \<in> GenericRootUniverse"
    by (rule unlocked_tick_current_generic_rootI[OF role])
  have count:
    "unat (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) ?lp)) =
       length (ring (generic_abs ?lp))"
    using GenericRootFamilyCoverage_count_cursorD[OF coverage root]
    by simp
  have abs_root:
    "generic_abs ?lp = current_delayed_ring a"
    by (rule unlocked_tick_current_generic_projectionD[
          OF role projection])
  show ?thesis
    using count abs_root
    by (simp add: generated_current_delayed_count_def abi_list_count_h_val)
qed

lemma unlocked_tick_current_delayed_root_guardD:
  assumes role: "scheduler_role_rel generated_scheduler_roots c a"
  shows
    "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
proof -
  have root:
    "abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)
       \<in> GenericRootUniverse"
    by (rule unlocked_tick_current_generic_rootI[OF role])
  have raw_guard:
    "c_guard
       (abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c))"
    using GenericRootUniverse_guarded root by blast
  show ?thesis
    using raw_guard by (rule iffD1[OF abi_list_ptr_c_guard])
qed

lemma unlocked_tick_current_delayed_generic_headD:
  assumes coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs M K_G"
    and role: "scheduler_role_rel generated_scheduler_roots c a"
    and projection:
      "strong_generic_role_projection a termination generic_abs"
    and observation:
      "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a M"
    and head:
      "ring (current_delayed_ring a) = Generic task # rest"
  shows
    "generated_current_delayed_count c \<noteq> 0 \<and>
     c_guard (generated_current_delayed_head c) \<and>
     generated_current_delayed_result c = sd_tcb_ptr D task"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source_lp =
    "(Scheduler_V611_Parse.globals.pxDelayedTaskList_' c ::
       Scheduler_V611_Parse.xLIST_C ptr)"
  let ?raw_lp = "abi_list_ptr ?source_lp"
  have root: "?raw_lp \<in> GenericRootUniverse"
    by (rule unlocked_tick_current_generic_rootI[OF role])
  have raw: "raw_xlist_rel ?h ?raw_lp (generic_raw ?raw_lp)"
    by (rule GenericRootFamilyCoverage_raw_rootD[OF coverage root])
  have relabel:
    "xlist_relabel (sd_node_decode D) (generic_raw ?raw_lp)
       (generic_abs ?raw_lp)"
    by (rule GenericRootFamilyCoverage_relabelD[OF coverage root])
  have abs_root: "generic_abs ?raw_lp = current_delayed_ring a"
    by (rule unlocked_tick_current_generic_projectionD[
          OF role projection])
  have lists:
    "sched_xlist_rel (sd_node_decode D) ?h ?raw_lp
       (current_delayed_ring a)"
    unfolding sched_xlist_rel_def
    apply (rule exI[where x="generic_raw ?raw_lp"])
    using raw relabel abs_root by simp
  have decode:
    "scheduler_decode_rel D (managed_scheduler_view a M)"
    by (rule GenericRootFamilyCoverage_managed_view_decodeD[
          OF coverage])
  have obs:
    "TaskObservationRel D ?h (managed_scheduler_view a M)"
    using observation
    by (simp add: scheduler_managed_task_observation_rel_def)
  have represented:
    "scheduler_list_head_item ?h ?source_lp =
       scheduler_generic_item_ptr (sd_tcb_ptr D task) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val ?h (scheduler_list_head_item ?h ?source_lp)) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D task)"
    using represented_generic_head_owner_priority[
      OF lists decode obs head]
    by blast
  have task_managed: "task \<in> M"
  proof -
    have decoded:
      "sd_node_decode D
         (abi_item_ptr (scheduler_list_head_item ?h ?source_lp)) =
       Some (Generic task)"
      by (rule sched_xlist_rel_head_decode[OF lists head])
    have laws: "universal_decoder_laws M D"
      by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
    show ?thesis
      using iffD1[OF universal_node_decode_Generic_iff[OF laws] decoded]
      by simp
  qed
  have task_live_view:
    "task \<in> sa_live (managed_scheduler_view a M)"
    using task_managed by (simp add: managed_scheduler_view_def)
  have task_fields:
    "c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D task))"
    using TaskObservationRel_liveD[OF obs task_live_view] by simp
  have generated_head:
    "generated_current_delayed_head c =
       scheduler_generic_item_ptr (sd_tcb_ptr D task)"
    using represented
    by (simp add: generated_current_delayed_head_def)
  have head_guard: "c_guard (generated_current_delayed_head c)"
    using generated_head task_fields by simp
  have count:
    "unat (generated_current_delayed_count c) =
       length (ring (current_delayed_ring a))"
    by (rule unlocked_tick_current_delayed_countD[
          OF coverage role projection])
  have nonempty: "generated_current_delayed_count c \<noteq> 0"
    using count head by auto
  have represented_owner:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val ?h (scheduler_list_head_item ?h ?source_lp)) =
     PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
       (sd_tcb_ptr D task)"
    by (rule conjunct2[OF represented])
  have generated_owner:
    "generated_current_delayed_owner c =
     PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
       (sd_tcb_ptr D task)"
    using represented_owner
    by (simp only: generated_current_delayed_owner_def
        generated_current_delayed_head_def)
  have owner_result:
    "PTR_COERCE(unit \<rightarrow>
       Scheduler_V611_Parse.tskTaskControlBlock_C)
       (generated_current_delayed_owner c) = sd_tcb_ptr D task"
    using generated_owner by simp
  have result:
    "generated_current_delayed_result c = sd_tcb_ptr D task"
    using nonempty owner_result
    by (simp add: generated_current_delayed_result_def)
  show ?thesis using nonempty head_guard result by blast
qed

theorem unlocked_tick_managed_physical_pointer_bridge:
  assumes coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs M K_G"
    and role: "scheduler_role_rel generated_scheduler_roots c a"
    and projection:
      "strong_generic_role_projection a termination generic_abs"
    and observation:
      "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a M"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof -
  have root_guard:
    "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    by (rule unlocked_tick_current_delayed_root_guardD[OF role])
  have count:
    "unat (generated_current_delayed_count c) =
       length (ring (current_delayed_ring a))"
    by (rule unlocked_tick_current_delayed_countD[
          OF coverage role projection])
  show ?thesis
  proof (cases due_tasks)
    case (Cons task due_tail)
    have ring_head:
      "ring (current_delayed_ring a) =
       Generic task # (map Generic due_tail @ map Generic future)"
      using split Cons by simp
    have physical:
      "generated_current_delayed_count c \<noteq> 0 \<and>
       c_guard (generated_current_delayed_head c) \<and>
       generated_current_delayed_result c = sd_tcb_ptr D task"
      by (rule unlocked_tick_current_delayed_generic_headD[
            OF coverage role projection observation ring_head])
    show ?thesis
      using root_guard physical Cons
      by (simp add: generated_current_delayed_readable_def
          unlocked_tick_entry_pointer_rel_def strong_due_next_ptr_rel_def)
  next
    case Nil
    note due_empty = Nil
    show ?thesis
    proof (cases future)
      case (Cons task future_tail)
      have ring_head:
        "ring (current_delayed_ring a) = Generic task # map Generic future_tail"
        using split due_empty Cons by simp
      have physical:
        "generated_current_delayed_count c \<noteq> 0 \<and>
         c_guard (generated_current_delayed_head c) \<and>
         generated_current_delayed_result c = sd_tcb_ptr D task"
        by (rule unlocked_tick_current_delayed_generic_headD[
              OF coverage role projection observation ring_head])
      show ?thesis
        using root_guard physical due_empty Cons
        by (simp add: generated_current_delayed_readable_def
            unlocked_tick_entry_pointer_rel_def strong_due_next_ptr_rel_def)
    next
      case Nil
      note future_empty = Nil
      have ring_empty: "ring (current_delayed_ring a) = []"
        using split due_empty future_empty by simp
      have count_empty: "generated_current_delayed_count c = 0"
        using count ring_empty by (simp add: unat_eq_0)
      have result_empty: "generated_current_delayed_result c = NULL"
        using count_empty
        by (simp add: generated_current_delayed_result_def)
      show ?thesis
        using root_guard count_empty result_empty due_empty future_empty
        by (simp add: generated_current_delayed_readable_def
            unlocked_tick_entry_pointer_rel_def strong_due_next_ptr_rel_def)
    qed
  qed
qed

corollary StrongSchedulerSnapshotRel_current_pointer_bridge:
  assumes snapshot:
    "StrongSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof -
  have coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs M K_G"
    by (rule StrongSchedulerSnapshotRel_generic_coverageD[OF snapshot])
  have projection:
    "strong_generic_role_projection a termination generic_abs"
    by (rule StrongSchedulerSnapshotRel_generic_projectionD[OF snapshot])
  have role: "scheduler_role_rel generated_scheduler_roots c a"
    using StrongSchedulerSnapshotRel_role_scalar_currentD[OF snapshot]
    by simp
  have observation:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a M"
    by (rule StrongSchedulerSnapshotRel_managed_observationD[OF snapshot])
  show ?thesis
    by (rule unlocked_tick_managed_physical_pointer_bridge[
          OF coverage role projection observation split])
qed

corollary DueLoopSchedulerSnapshotRel_current_pointer_bridge:
  assumes snapshot:
    "DueLoopSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future_nodes"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof -
  have coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs M K_G"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have projection:
    "strong_generic_role_projection a termination generic_abs"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have role: "scheduler_role_rel generated_scheduler_roots c a"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have observation:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a M"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  show ?thesis
    by (rule unlocked_tick_managed_physical_pointer_bridge[
          OF coverage role projection observation split])
qed

theorem unlocked_tick_entry_snapshot_pointer_bridge:
  assumes snapshot:
    "case due_tasks of
       [] \<Rightarrow>
         StrongSchedulerSnapshotRel D c a M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         DueLoopSchedulerSnapshotRel D c a M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
           now (map Generic (task # due_tail)) (map Generic future)"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof (cases due_tasks)
  case Nil
  have stable:
    "StrongSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using snapshot Nil by simp
  show ?thesis
    by (rule StrongSchedulerSnapshotRel_current_pointer_bridge[
          OF stable split])
next
  case (Cons task due_tail)
  have loop:
    "DueLoopSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now (map Generic (task # due_tail)) (map Generic future)"
    using snapshot Cons by simp
  show ?thesis
    by (rule DueLoopSchedulerSnapshotRel_current_pointer_bridge[
          OF loop split])
qed

theorem StrongUnlockedTickManagedEntryAssemblerRel_physical_pointer_bridge:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "generated_current_delayed_readable entry_c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result entry_c)"
proof -
  have exit:
    "due_prefix_exit_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future))"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel])
  have base:
    "due_prefix_loop_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have split:
    "ring (current_delayed_ring entry) =
       map Generic due_tasks @ map Generic future"
    by (rule due_prefix_loop_inv_ringD[OF base])
  have snapshot:
    "case due_tasks of
       [] \<Rightarrow>
         StrongSchedulerSnapshotRel D entry_c entry M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         DueLoopSchedulerSnapshotRel D entry_c entry M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
           now (map Generic (task # due_tail)) (map Generic future)"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_snapshotD[OF rel])
  show ?thesis
    by (rule unlocked_tick_entry_snapshot_pointer_bridge[
          OF snapshot split])
qed

end
