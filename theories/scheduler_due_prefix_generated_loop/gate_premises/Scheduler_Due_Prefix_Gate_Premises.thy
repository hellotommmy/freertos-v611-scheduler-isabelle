theory Scheduler_Due_Prefix_Gate_Premises
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tick_Loop.Scheduler_One_Due_Task_Phases_Tick_Loop"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Pure_Frame.Scheduler_Due_Prefix_Pure_Frame"
begin

text \<open>
  Removing the current delayed-list head commutes with the Gate-H decoder.
  This is the reusable form of the relabel/remove argument: it keeps every
  task, root, cursor, raw family and heap symbolic.
\<close>

theorem one_due_gateH_removed_relabel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "xlist_relabel (sd_node_decode D)
       (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))
       (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C)))"
proof -
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have source_root: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have relabel:
    "xlist_relabel (sd_node_decode D) (generic_raw ?source)
       (ods_generic_family S ?source)"
    by (rule one_due_gateH_relabelD[OF rel source_root])
  have raw_wf: "xlist_wf (generic_raw ?source)"
    by (rule raw_xlist_rel_wf[OF
        one_due_gateH_raw_xlist_relD[OF rel source_root]])
  have p_decode:
    "sd_node_decode D ?p = Some (Generic (odc_task C))"
    by (rule one_due_gateH_task_ptr_decode[OF rel])
  show ?thesis
    by (rule xlist_relabel_remove[
          OF relabel raw_wf p_decode
             one_due_gateH_ring_decode_inj[OF rel source_root]])
qed

text \<open>
  Consequently, deletion leaves an empty concrete residual ring exactly when
  it leaves an empty abstract residual ring.  In particular, last-due exit is
  derived from representation rather than assumed as a concrete branch fact.
\<close>

theorem one_due_gateH_removed_empty_iff:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) = [] \<longleftrightarrow>
     ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) = []"
proof -
  have relabel:
    "xlist_relabel (sd_node_decode D)
       (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))
       (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C)))"
    by (rule one_due_gateH_removed_relabel[OF rel])
  have length_eq:
    "length (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
     length (ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))))"
    by (rule xlist_relabel_ring_length[OF relabel])
  show ?thesis
  proof
    assume raw_empty:
      "ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C))) = []"
    have
      "length (ring (list_remove_abs (Generic (odc_task C))
        (ods_generic_family S (odc_delayed_root C)))) = 0"
      using length_eq raw_empty by simp
    then show
      "ring (list_remove_abs (Generic (odc_task C))
        (ods_generic_family S (odc_delayed_root C))) = []"
      by simp
  next
    assume abs_empty:
      "ring (list_remove_abs (Generic (odc_task C))
        (ods_generic_family S (odc_delayed_root C))) = []"
    have
      "length (ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C)))) = 0"
      using length_eq abs_empty by simp
    then show
      "ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C))) = []"
      by simp
  qed
qed

text \<open>
  Decoder bridge from the abstract residual head to the concrete residual
  head.  This is deliberately stated for arbitrary decoded tasks, rings,
  cursors and heaps.  It closes the direction that the existing owner-read
  theorem cannot provide: an abstract nonempty successor identifies the
  concrete nonempty successor before the generated tail read is executed.
\<close>

theorem one_due_gateH_removed_head_bridge:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and head:
      "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C))) =
       Generic u # rest"
  shows
    "u \<in> odc_live C \<and>
     ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> [] \<and>
     hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D u"
proof -
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have source_root: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have removed_relabel:
    "xlist_relabel (sd_node_decode D)
       (list_remove_abs ?p (generic_raw ?source))
       (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S ?source))"
    by (rule one_due_gateH_removed_relabel[OF rel])
  obtain rest where abs_ring:
    "ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S ?source)) = Generic u # rest"
    using head by blast
  have pairs:
    "list_all2 (\<lambda>q n. sd_node_decode D q = Some n)
       (ring (list_remove_abs ?p (generic_raw ?source)))
       (Generic u # rest)"
    using removed_relabel abs_ring
    by (simp add: xlist_relabel_def)
  obtain q qs where raw_ring:
      "ring (list_remove_abs ?p (generic_raw ?source)) = q # qs"
    and q_decode: "sd_node_decode D q = Some (Generic u)"
    using pairs
    by (cases "ring (list_remove_abs ?p (generic_raw ?source))") auto
  have post_member:
    "Generic u \<in> set (ring (list_remove_abs
       (Generic (odc_task C)) (ods_generic_family S ?source)))"
    using abs_ring by simp
  have removed_subset:
    "set (ring (list_remove_abs
       (Generic (odc_task C)) (ods_generic_family S ?source)))
       \<subseteq> set (ring (ods_generic_family S ?source))"
    by (rule list_remove_abs_ring_subset)
  have u_old:
    "Generic u \<in> set (ring (ods_generic_family S ?source))"
    using post_member removed_subset by blast
  have shape: "one_due_family_shape C S"
    using one_due_gateH_pure_entryD[OF rel]
    by (simp add: one_due_entry_rel_def)
  have u_live: "u \<in> odc_live C"
    using shape source_root u_old
    by (auto simp: one_due_family_shape_def)
  have u_decode:
    "sd_node_decode D (one_due_generic_raw_ptr D u) =
       Some (Generic u)"
    by (rule one_due_gateH_generic_ptr_decode[OF rel u_live])
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have q_eq: "q = one_due_generic_raw_ptr D u"
    by (rule one_due_generic_decode_inj[OF laws q_decode u_decode])
  show ?thesis
    using u_live raw_ring q_eq by simp
qed

text \<open>
  A non-NULL first future head is the exceptional terminal branch of the
  generated loop.  The while condition itself remains true; the body reads
  the observed Generic key and throws before any list mutation is reached.
\<close>

theorem one_due_tick_future_head_throws:
  assumes obs:
      "TaskObservationRel D
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    and live: "u \<in> sa_live a"
    and tick:
      "Scheduler_V611_Parse.globals.xTickCount_' c = now"
    and key:
      "raw_key_at
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (one_due_generic_raw_ptr D u) = k"
    and future: "now < k"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D u) \<bullet> c
     \<lbrace>\<lambda>r t. r = Exn () \<and> t = c\<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?tp = "sd_tcb_ptr D u"
  note observed = TaskObservationRel_liveD[OF obs live]
  have guard_item: "c_guard (scheduler_generic_item_ptr ?tp)"
    using observed by blast
  have guard_tcb: "c_guard ?tp"
    using observed by blast
  have key_read:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
         (h_val ?h ?tp)) = k"
    using one_due_tcb_generic_key_read[of ?h ?tp] key
    by (simp add: one_due_generic_raw_ptr_def)
  have compare:
    "Scheduler_V611_Parse.globals.xTickCount_' c <
       Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
           (h_val ?h ?tp))"
    using tick key_read future by simp
  show ?thesis
    unfolding one_due_tick_loop_body_source_def
    apply runs_to_vcg
    subgoal by (rule guard_item)
    subgoal by (rule guard_tcb)
    subgoal using compare by simp
    done
qed

end
