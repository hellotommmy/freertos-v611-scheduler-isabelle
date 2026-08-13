theory Scheduler_Due_Prefix_Pure_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_Pure.Scheduler_One_Due_Task_Phases_Reentry_Pure"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Invariant.Scheduler_Due_Prefix_Invariant"
begin

text \<open>
  Pure frame facts connecting one completed generated due-task phase to the
  arbitrary due-prefix fold.  Every task, root, prefix, ring, priority map,
  tick and abstract scheduler state remains universally quantified.
\<close>

lemma due_prefix_remove_nodes_item_key [simp]:
  "item_key (remove_nodes ns q) = item_key q"
  by (induction ns arbitrary: q)
     (simp_all add: remove_nodes_def list_remove_abs_item_key)

lemma due_prefix_fold_state_current_delayed_item_key [simp]:
  "item_key
     (current_delayed_ring (due_prefix_fold_state entry processed)) =
   item_key (current_delayed_ring entry)"
  by simp

definition one_due_all_ready_destinations ::
  "('tid, 'root) one_due_context \<Rightarrow> bool"
where
  "one_due_all_ready_destinations C \<longleftrightarrow>
     (\<forall>t\<in>odc_live C.
        odc_ready_root C (odc_priority C t) \<in> odc_generic_roots C \<and>
        odc_delayed_root C \<noteq>
          odc_ready_root C (odc_priority C t))"

lemma one_due_all_ready_destinationsD:
  assumes destinations: "one_due_all_ready_destinations C"
    and live: "t \<in> odc_live C"
  shows
    "odc_ready_root C (odc_priority C t) \<in> odc_generic_roots C \<and>
     odc_delayed_root C \<noteq>
       odc_ready_root C (odc_priority C t)"
  using destinations live
  by (auto simp: one_due_all_ready_destinations_def)

lemma one_due_all_ready_destinations_reentry [simp]:
  "one_due_all_ready_destinations (one_due_reentry_context C u) \<longleftrightarrow>
   one_due_all_ready_destinations C"
  by (simp add: one_due_all_ready_destinations_def
      one_due_reentry_context_components)

lemma one_due_reentry_snapshot_pending_empty:
  assumes entry: "one_due_entry_rel C branch S"
    and pending_empty:
      "ring (ods_event_family S (odc_pending_root C)) = []"
  shows
    "ring (ods_event_family (one_due_reentry_snapshot C branch S)
       (odc_pending_root C)) = []"
proof (cases branch)
  case (DueEventLinked owner)
  have external: "owner \<in> one_due_external_roots C"
    using entry DueEventLinked
    by (simp add: one_due_entry_rel_def)
  have owner_not_pending: "owner \<noteq> odc_pending_root C"
    using external
    by (auto simp: one_due_external_roots_def)
  show ?thesis
    using pending_empty owner_not_pending DueEventLinked
    by (simp add: one_due_reentry_snapshot_event_at)
next
  case DueEventNull
  show ?thesis
    using pending_empty DueEventNull
    by (simp add: one_due_reentry_snapshot_event_at)
qed

corollary one_due_reentry_context_pending_empty:
  assumes entry: "one_due_entry_rel C branch S"
    and pending_empty:
      "ring (ods_event_family S (odc_pending_root C)) = []"
  shows
    "ring (ods_event_family (one_due_reentry_snapshot C branch S)
       (odc_pending_root (one_due_reentry_context C u))) = []"
  using one_due_reentry_snapshot_pending_empty[OF entry pending_empty]
  by (simp add: one_due_reentry_context_components)

lemma one_due_reentry_delayed_matches_due_prefix_result_step:
  assumes current: "current = due_prefix_fold_state entry processed"
    and delayed:
      "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    and target_distinct:
      "odc_delayed_root C \<noteq> one_due_target_root C"
  shows
    "ods_generic_family (one_due_reentry_snapshot C branch S)
       (odc_delayed_root C) =
     current_delayed_ring
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))"
proof -
  have snapshot_delayed:
    "ods_generic_family (one_due_reentry_snapshot C branch S)
       (odc_delayed_root C) =
     list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))"
    using target_distinct
    by (simp add: one_due_reentry_snapshot_generic_at Let_def)
  have step:
    "due_prefix_result_step_abs entry processed (Generic (odc_task C)) =
     add_ready_node (Generic (odc_task C))
       (put_current_delayed
         (list_remove_abs (Generic (odc_task C))
           (current_delayed_ring current)) current)"
    by (rule due_prefix_result_step_is_one_generic_step[OF current refl])
  have result_delayed:
    "current_delayed_ring
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) =
     list_remove_abs (Generic (odc_task C))
       (current_delayed_ring current)"
  proof -
    have congruence:
      "current_delayed_ring
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) =
       current_delayed_ring
         (add_ready_node (Generic (odc_task C))
           (put_current_delayed
             (list_remove_abs (Generic (odc_task C))
               (current_delayed_ring current)) current))"
      by (rule arg_cong[OF step])
    show ?thesis
      using congruence
      by (simp only: due_add_ready_frames_current_delayed
          due_current_delayed_after_put)
  qed
  show ?thesis
    using snapshot_delayed result_delayed delayed by simp
qed

text \<open>
  The due-prefix fold changes ready ownership, wake/event observations and the
  top-ready hint, but it frames the live carrier, the total priority map and
  the current tick.  These are exactly the abstract fields observed by the
  Gate-H task-observation index (with the tick exported for the loop ledger).
\<close>

lemma due_prefix_pure_add_ready_live [simp]:
  "sa_live (add_ready_node n s) = sa_live s"
  by (cases n) (simp_all add: Let_def)

lemma due_prefix_pure_add_ready_priority [simp]:
  "sa_priority (add_ready_node n s) = sa_priority s"
  by (cases n) (simp_all add: Let_def)

lemma due_prefix_pure_add_ready_tick [simp]:
  "sa_tick (add_ready_node n s) = sa_tick s"
  by (cases n) (simp_all add: Let_def)

lemma due_prefix_pure_fold_add_ready_live [simp]:
  "sa_live (fold add_ready_node ns s) = sa_live s"
  by (induction ns arbitrary: s) simp_all

lemma due_prefix_pure_fold_add_ready_priority [simp]:
  "sa_priority (fold add_ready_node ns s) = sa_priority s"
  by (induction ns arbitrary: s) simp_all

lemma due_prefix_pure_fold_add_ready_tick [simp]:
  "sa_tick (fold add_ready_node ns s) = sa_tick s"
  by (induction ns arbitrary: s) simp_all

lemma due_prefix_pure_put_current_live [simp]:
  "sa_live (put_current_delayed q s) = sa_live s"
  by (cases "sa_current_role_a s")
     (simp_all add: put_current_delayed_def)

lemma due_prefix_pure_put_current_priority [simp]:
  "sa_priority (put_current_delayed q s) = sa_priority s"
  by (cases "sa_current_role_a s")
     (simp_all add: put_current_delayed_def)

lemma due_prefix_pure_put_current_tick [simp]:
  "sa_tick (put_current_delayed q s) = sa_tick s"
  by (cases "sa_current_role_a s")
     (simp_all add: put_current_delayed_def)

lemma due_prefix_fold_state_live [simp]:
  "sa_live (due_prefix_fold_state entry processed) = sa_live entry"
  by (simp add: due_prefix_fold_state_def)

lemma due_prefix_fold_state_priority [simp]:
  "sa_priority (due_prefix_fold_state entry processed) = sa_priority entry"
  by (simp add: due_prefix_fold_state_def)

lemma due_prefix_fold_state_tick [simp]:
  "sa_tick (due_prefix_fold_state entry processed) = sa_tick entry"
  by (simp add: due_prefix_fold_state_def)

lemma due_prefix_result_step_abs_live [simp]:
  "sa_live (due_prefix_result_step_abs entry processed n) = sa_live entry"
  by (simp add: due_prefix_result_step_abs_def)

lemma due_prefix_result_step_abs_priority [simp]:
  "sa_priority (due_prefix_result_step_abs entry processed n) =
   sa_priority entry"
  by (simp add: due_prefix_result_step_abs_def)

lemma due_prefix_result_step_abs_tick [simp]:
  "sa_tick (due_prefix_result_step_abs entry processed n) = sa_tick entry"
  by (simp add: due_prefix_result_step_abs_def)

lemma due_prefix_result_step_task_observation_iff:
  "TaskObservationRel D h (due_prefix_result_step_abs entry processed n) \<longleftrightarrow>
   TaskObservationRel D h entry"
  by (simp add: TaskObservationRel_def)

lemma one_due_gateH_entry_rel_abs_param_cong:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "sa_live a' = sa_live a"
    and priority: "sa_priority a' = sa_priority a"
  shows
    "one_due_gateH_entry_rel D R c a' C branch S generic_raw event_raw"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have obs: "TaskObservationRel D ?h a"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have obs': "TaskObservationRel D ?h a'"
    using obs live priority
    by (auto simp: TaskObservationRel_def)
  have live_old: "odc_live C = sa_live a"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have priority_old:
    "\<forall>t\<in>odc_live C. odc_priority C t = sa_priority a t"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have live': "odc_live C = sa_live a'"
    using live_old live by simp
  have priority':
    "\<forall>t\<in>odc_live C. odc_priority C t = sa_priority a' t"
    using priority_old priority by simp
  show ?thesis
    using rel obs' live' priority'
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
qed

theorem one_due_gateH_entry_rel_due_prefix_result_step:
  assumes rel:
    "one_due_gateH_entry_rel D R c
       (due_prefix_fold_state entry processed)
       C branch S generic_raw event_raw"
  shows
    "one_due_gateH_entry_rel D R c
       (due_prefix_result_step_abs entry processed n)
       C branch S generic_raw event_raw"
  by (rule one_due_gateH_entry_rel_abs_param_cong[OF rel]) simp_all

end
