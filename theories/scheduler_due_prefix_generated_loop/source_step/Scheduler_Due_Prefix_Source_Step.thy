theory Scheduler_Due_Prefix_Source_Step
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Gate_Premises.Scheduler_Due_Prefix_Gate_Premises"
begin

text \<open>
  The generated loop-head invariant couples the concrete Gate-H relation to
  the arbitrary due-prefix ledger.  It also records the few cross-layer facts
  that are not fields of either component: the common tick, the delayed-family
  view, readiness of every legal destination, and emptiness of the pending
  Event root used to derive the next Event branch.  No task, priority, tick,
  ring length, cursor, address, decoder, or branch is fixed.
\<close>

definition due_prefix_gate_inv ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid scheduler_abs \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw \<longleftrightarrow>
     one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw \<and>
     due_prefix_loop_inv now entry processed remaining future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"

text \<open>
  One normal generated body execution consumes the arbitrary current due head
  and selects the arbitrary next due head.  The successor Event branch is an
  existential output, derived from the represented finite Event family after
  the current task has been removed.  The exact generated heaps and globals
  exported by @{thm one_due_tick_gate_step} are retained in the successor
  invariant.
\<close>

theorem due_prefix_generated_source_result_step:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       (Generic (odc_task C) # Generic u # remaining) future
       current C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)\<rbrace>"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using inv by (simp add: due_prefix_gate_inv_def)
  have prefix:
    "due_prefix_loop_inv now entry processed
       (Generic (odc_task C) # Generic u # remaining) future current"
    using inv by (simp add: due_prefix_gate_inv_def)
  have context_tick: "odc_tick C = now"
    using inv by (simp add: due_prefix_gate_inv_def)
  have abstract_tick: "sa_tick current = now"
    using inv by (simp add: due_prefix_gate_inv_def)
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    using inv by (simp add: due_prefix_gate_inv_def)
  have destinations: "one_due_all_ready_destinations C"
    using inv by (simp add: due_prefix_gate_inv_def)
  have pending_empty:
    "ring (ods_event_family S (odc_pending_root C)) = []"
    using inv by (simp add: due_prefix_gate_inv_def)

  have current_def:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF prefix])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic (odc_task C) # Generic u # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF prefix] by simp
  have snapshot_ring:
    "ring (ods_generic_family S (odc_delayed_root C)) =
       Generic (odc_task C) # Generic u # (remaining @ future)"
    using delayed current_ring by simp
  have head_shape:
    "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) =
       Generic u # rest"
    using snapshot_ring
    by (auto simp: list_remove_abs_def)

  note head_bridge = one_due_gateH_removed_head_bridge[OF rel head_shape]
  have u_live: "u \<in> odc_live C"
    using head_bridge by blast
  have raw_nonempty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> []"
    using head_bridge by blast
  have raw_head:
    "hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D u"
    using head_bridge by blast

  have due_split:
    "due_nodes now (current_delayed_ring entry) =
       processed @
         (Generic (odc_task C) # Generic u # remaining)"
    by (rule due_prefix_loop_inv_due_splitD[OF prefix])
  have u_in_due:
    "Generic u \<in> set (due_nodes now (current_delayed_ring entry))"
    using due_split by auto
  have u_due_at_entry:
    "item_key (current_delayed_ring entry) (Generic u) \<le> now"
    by (rule due_nodes_member_is_due[OF u_in_due])

  have entry_rel: "one_due_entry_rel C branch S"
    by (rule one_due_gateH_pure_entryD[OF rel])
  have source_root:
    "odc_delayed_root C \<in> odc_generic_roots C"
    using entry_rel
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have shape: "one_due_family_shape C S"
    using entry_rel by (simp add: one_due_entry_rel_def)
  have u_in_snapshot:
    "Generic u \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using snapshot_ring by simp
  have u_snapshot_key:
    "item_key (ods_generic_family S (odc_delayed_root C))
       (Generic u) = ods_generic_payload S u"
    using shape source_root u_live u_in_snapshot
    by (auto simp: one_due_family_shape_def)
  have u_current_key:
    "item_key (current_delayed_ring current) (Generic u) =
       ods_generic_payload S u"
    using delayed u_snapshot_key by simp
  have u_entry_key:
    "item_key (current_delayed_ring entry) (Generic u) =
       ods_generic_payload S u"
    using current_def u_current_key by simp
  have u_due: "ods_generic_payload S u \<le> odc_tick C"
    using u_due_at_entry u_entry_key context_tick by simp

  note target = one_due_all_ready_destinationsD[OF destinations u_live]
  have target_root:
    "odc_ready_root C (odc_priority C u) \<in> odc_generic_roots C"
    using target by blast
  have target_distinct:
    "odc_delayed_root C \<noteq>
       odc_ready_root C (odc_priority C u)"
    using target by blast

  have reentry_pending_empty:
    "ring (ods_event_family (one_due_reentry_snapshot C branch S)
       (odc_pending_root (one_due_reentry_context C u))) = []"
    by (rule one_due_reentry_context_pending_empty[
          OF entry_rel pending_empty])
  obtain branch' where next_branch:
    "one_due_event_branch_at (one_due_reentry_context C u)
       (one_due_reentry_snapshot C branch S) branch'"
    using one_due_event_branch_exhaustive_if_pending_empty[
      OF reentry_pending_empty]
    by blast

  have source_target_distinct:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using entry_rel
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have post_prefix:
    "due_prefix_loop_inv now entry
       (processed @ [Generic (odc_task C)])
       (Generic u # remaining) future
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))"
    by (rule due_prefix_result_step_preserves_inv[OF prefix])
  have entry_tick: "sa_tick entry = now"
    using abstract_tick current_def by simp
  have post_abstract_tick:
    "sa_tick (due_prefix_result_step_abs entry processed
       (Generic (odc_task C))) = now"
    using entry_tick by simp
  have post_context_tick:
    "odc_tick (one_due_reentry_context C u) = now"
    using context_tick
    by (simp add: one_due_reentry_context_components)
  have post_delayed:
    "ods_generic_family (one_due_reentry_snapshot C branch S)
       (odc_delayed_root (one_due_reentry_context C u)) =
     current_delayed_ring
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))"
  proof -
    have old_root:
      "ods_generic_family (one_due_reentry_snapshot C branch S)
         (odc_delayed_root C) =
       current_delayed_ring
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C)))"
      by (rule one_due_reentry_delayed_matches_due_prefix_result_step[
            OF current_def delayed source_target_distinct])
    show ?thesis
      using old_root
      by (simp add: one_due_reentry_context_components)
  qed
  have post_destinations:
    "one_due_all_ready_destinations (one_due_reentry_context C u)"
    using destinations by simp

  have source_step:
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. r = Result (sd_tcb_ptr D u) \<and>
        one_due_gateH_entry_rel D R t current
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)\<rbrace>"
    by (rule one_due_tick_gate_step[
          OF rel roots u_live raw_nonempty raw_head head_shape u_due
             target_root target_distinct next_branch])

  show ?thesis
  proof (rule runs_to_weaken[OF source_step])
    fix r t
    assume step_post:
      "r = Result (sd_tcb_ptr D u) \<and>
       one_due_gateH_entry_rel D R t current
         (one_due_reentry_context C u) branch'
         (one_due_reentry_snapshot C branch S)
         (one_due_reentry_generic_raw D C
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem
                 (Scheduler_V611_Parse.globals.t_hrs_' c))))
           generic_raw)
         (one_due_event_raw_after_remove D C branch event_raw)"
    have result: "r = Result (sd_tcb_ptr D u)"
      using step_post by blast
    have gate_old:
      "one_due_gateH_entry_rel D R t current
         (one_due_reentry_context C u) branch'
         (one_due_reentry_snapshot C branch S)
         (one_due_reentry_generic_raw D C
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem
                 (Scheduler_V611_Parse.globals.t_hrs_' c))))
           generic_raw)
         (one_due_event_raw_after_remove D C branch event_raw)"
      using step_post by blast
    have live_frame:
      "sa_live (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) = sa_live current"
      using current_def by simp
    have priority_frame:
      "sa_priority (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) = sa_priority current"
      using current_def by simp
    have gate_new:
      "one_due_gateH_entry_rel D R t
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C)))
         (one_due_reentry_context C u) branch'
         (one_due_reentry_snapshot C branch S)
         (one_due_reentry_generic_raw D C
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem
                 (Scheduler_V611_Parse.globals.t_hrs_' c))))
           generic_raw)
         (one_due_event_raw_after_remove D C branch event_raw)"
      by (rule one_due_gateH_entry_rel_abs_param_cong[
            OF gate_old live_frame priority_frame])
    show
      "\<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)"
    proof (rule exI[of _ branch'], rule conjI)
      show "r = Result (sd_tcb_ptr D u)"
        by (rule result)
      show
        "due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)"
        unfolding due_prefix_gate_inv_def
        using gate_new post_prefix post_context_tick post_abstract_tick
          post_delayed post_destinations reentry_pending_empty
        by blast
    qed
  qed
qed

end
