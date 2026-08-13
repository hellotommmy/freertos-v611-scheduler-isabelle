theory Scheduler_One_Due_Task_Phases_Tick_Loop
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_GateH.Scheduler_One_Due_Task_Phases_Reentry_GateH"
begin

text \<open>
  The complete due-iteration of the generated delayed-task loop body.
  At a gate state the two guards discharge from the observation, the
  due-compare condition takes the skip branch because the gate carries
  the head's dueness, and the residual Generic remove, Event dispatch
  and top/ready tail execute through the accepted cutpoints down to
  the delayed-head remainder, whose continuation receives the exact
  insert heap and the pinned globals.
\<close>

lemma one_due_tcb_generic_key_read:
  "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
     (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
       (h_val h tp)) =
   raw_key_at h (abi_generic_list_item_ptr tp)"
  by (simp add: raw_key_at_def abi_generic_list_item_ptr_def
      scheduler_generic_item_ptr_def abi_item_key_h_val
      flip: scheduler_generic_item_h_val)

lemma one_due_gateH_head_dueD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "ods_generic_payload S (odc_task C) \<le> odc_tick C"
  using one_due_gateH_pure_entryD[OF rel]
  by (simp add: one_due_entry_rel_def)

lemma one_due_gateH_tick_wordD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "odc_tick C = Scheduler_V611_Parse.globals.xTickCount_' c"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

theorem one_due_tick_body_composed:
  fixes Q
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and cont:
      "\<And>t. hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
           one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))) \<Longrightarrow>
         Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
           Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<Longrightarrow>
         Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
           (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                  (sd_tcb_ptr D (odc_task C)))
            then
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                  (sd_tcb_ptr D (odc_task C)))
            else
              Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)
           \<Longrightarrow>
         Scheduler_V611_Parse.globals.xTickCount_' t =
           Scheduler_V611_Parse.globals.xTickCount_' c \<Longrightarrow>
         one_due_tick_delayed_remainder \<bullet> t \<lbrace>Q\<rbrace>"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and> Q (Result v) t\<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?tp = "sd_tcb_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have task_abs: "odc_task C \<in> sa_live a"
    using task_live one_due_gateH_live_absD[OF rel] by simp
  have obs:
    "TaskObservationRel D ?h a"
    by (rule one_due_gateH_task_observationD[OF rel])
  note obs_task = TaskObservationRel_liveD[OF obs task_abs]
  have guard_item:
    "c_guard (scheduler_generic_item_ptr ?tp)"
    using obs_task by blast
  have guard_tcb: "c_guard ?tp"
    using obs_task by blast
  have key_read:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
         (h_val ?h ?tp)) =
     ods_generic_payload S (odc_task C)"
    using one_due_tcb_generic_key_read[of ?h ?tp]
      one_due_gateH_generic_keysD[OF rel task_live]
    by (simp add: one_due_generic_raw_ptr_def)
  have not_due_false:
    "\<not> Scheduler_V611_Parse.globals.xTickCount_' c <
       Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
           (h_val ?h ?tp))"
    using key_read one_due_gateH_head_dueD[OF rel]
      one_due_gateH_tick_wordD[OF rel]
    by (simp add: not_less)
  have tail:
    "one_due_tick_top_ready_tail_source ?tp \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C ?h)) c)
     \<lbrace>Q\<rbrace>"
    by (rule one_due_tick_tail_insert_composed[OF rel roots cont])
  have inner:
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr ?tp))
       (\<lambda>_. one_due_tick_after_generic_source ?tp) \<bullet> c
     \<lbrace>Q\<rbrace>"
    by (rule one_due_generated_generic_event_then_top_ready_cutpoint[
      OF rel tail])
  show ?thesis
    unfolding one_due_tick_loop_body_source_def
    apply runs_to_vcg
    subgoal by (rule guard_item)
    subgoal by (rule guard_tcb)
    subgoal using not_due_false by simp
    subgoal
      apply (rule runs_to_weaken[OF
        inner[unfolded runs_to_bind_iff]])
      apply clarsimp
      apply (rule runs_to_weaken)
       apply assumption
      apply clarsimp
      done
    done
qed

definition one_due_tick_body_post ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr)
     exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "one_due_tick_body_post D C branch generic_raw c r t \<longleftrightarrow>
     hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
       one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) \<and>
     Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
       Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<and>
     Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
       (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
          Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
              (sd_tcb_ptr D (odc_task C)))
        then Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
              (sd_tcb_ptr D (odc_task C)))
        else Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)
     \<and>
     Scheduler_V611_Parse.globals.xTickCount_' t =
       Scheduler_V611_Parse.globals.xTickCount_' c \<and>
     r = Result (
       if ring (list_remove_abs
            (one_due_generic_raw_ptr D (odc_task C))
            (generic_raw (odc_delayed_root C))) = []
       then NULL
       else PTR_COERCE(unit \<rightarrow>
              Scheduler_V611_Parse.tskTaskControlBlock_C)
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
             (hd (ring (list_remove_abs
               (one_due_generic_raw_ptr D (odc_task C))
               (generic_raw (odc_delayed_root C))))))))"

theorem one_due_tick_body_exact:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result v) t\<rbrace>"
proof (rule one_due_tick_body_composed[OF rel roots])
  fix t :: "Scheduler_V611_Parse.globals"
  assume h:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
     one_due_ready_insert_heap D C generic_raw
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))"
    and d:
    "Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
     Scheduler_V611_Parse.globals.pxDelayedTaskList_' c"
    and p:
    "Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
     (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
        Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (sd_tcb_ptr D (odc_task C)))
      then Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (sd_tcb_ptr D (odc_task C)))
      else Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)"
    and k:
    "Scheduler_V611_Parse.globals.xTickCount_' t =
     Scheduler_V611_Parse.globals.xTickCount_' c"
  show "one_due_tick_delayed_remainder \<bullet> t
     \<lbrace>one_due_tick_body_post D C branch generic_raw c\<rbrace>"
    apply (rule runs_to_weaken[OF
      one_due_tick_delayed_remainder_exact[OF rel h d]])
    using h d p k
    by (auto simp: one_due_tick_body_post_def)
qed


lemma one_due_gateH_generic_ptr_decode:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "t \<in> odc_live C"
  shows
    "sd_node_decode D (one_due_generic_raw_ptr D t) =
       Some (Generic t)"
proof -
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have bullets:
    "\<forall>t\<in>odc_live C.
       sd_tcb_decode D (sd_tcb_ptr D t) = Some t \<and>
       sd_node_decode D
         (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
         Some (Generic t) \<and>
       sd_node_decode D
         (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
         Some (Event t)"
    using laws by (simp add: universal_decoder_laws_def)
  show ?thesis
    using bspec[OF bullets live]
    by (simp add: one_due_generic_raw_ptr_def)
qed

theorem one_due_tick_gate_step:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and u_live: "u \<in> odc_live C"
    and nonempty:
      "ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))) \<noteq> []"
    and hd_link:
      "hd (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D u"
    and head_shape:
      "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C))) =
       Generic u # rest"
    and u_due: "ods_generic_payload S u \<le> odc_tick C"
    and target'_root:
      "odc_ready_root C (odc_priority C u) \<in> odc_generic_roots C"
    and target'_ne:
      "odc_delayed_root C \<noteq> odc_ready_root C (odc_priority C u)"
    and branch':
      "one_due_event_branch_at (one_due_reentry_context C u)
         (one_due_reentry_snapshot C branch S) branch'"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C))
       \<bullet> c
     \<lbrace>\<lambda>r t. r = Result (sd_tcb_ptr D u) \<and>
        one_due_gateH_entry_rel D R t a
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch
            event_raw)\<rbrace>"
proof -
  have u_raw_member:
    "one_due_generic_raw_ptr D u \<in>
       set (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))))"
    using hd_in_set[OF nonempty] hd_link by simp
  obtain u' where u'_live: "u' \<in> odc_live C"
    and hd_eq:
      "hd (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D u'"
    and owner_val:
      "PTR_COERCE(unit \<rightarrow>
          Scheduler_V611_Parse.tskTaskControlBlock_C)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (hd (ring (list_remove_abs
              (one_due_generic_raw_ptr D (odc_task C))
              (generic_raw (odc_delayed_root C))))))) =
        sd_tcb_ptr D u'"
    using one_due_next_head_owner_decode[OF rel nonempty] by blast
  have ptr_eq:
    "one_due_generic_raw_ptr D u = one_due_generic_raw_ptr D u'"
    using hd_link hd_eq by simp
  have du:
    "sd_node_decode D (one_due_generic_raw_ptr D u) =
       Some (Generic u)"
    by (rule one_due_gateH_generic_ptr_decode[OF rel u_live])
  have du':
    "sd_node_decode D (one_due_generic_raw_ptr D u') =
       Some (Generic u')"
    by (rule one_due_gateH_generic_ptr_decode[OF rel u'_live])
  have decode_eq:
    "sd_node_decode D (one_due_generic_raw_ptr D u) =
     sd_node_decode D (one_due_generic_raw_ptr D u')"
    by (rule arg_cong[OF ptr_eq])
  have left:
    "Some (Generic u) =
     sd_node_decode D (one_due_generic_raw_ptr D u)"
    by (rule sym[OF du])
  have middle:
    "Some (Generic u) =
     sd_node_decode D (one_due_generic_raw_ptr D u')"
    by (rule trans[OF left decode_eq])
  have some_nodes: "Some (Generic u) = Some (Generic u')"
    by (rule trans[OF middle du'])
  have nodes: "Generic u = Generic u'"
    using some_nodes by (simp only: option.inject)
  have u_same: "u = u'"
    using nodes by (simp only: node_kind.inject)
  have u_eq: "u' = u" by (rule sym[OF u_same])
  have owner_u:
    "PTR_COERCE(unit \<rightarrow>
        Scheduler_V611_Parse.tskTaskControlBlock_C)
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          (hd (ring (list_remove_abs
            (one_due_generic_raw_ptr D (odc_task C))
            (generic_raw (odc_delayed_root C))))))) =
      sd_tcb_ptr D u"
    using owner_val u_eq by simp
  show ?thesis
  proof (rule runs_to_weaken[OF one_due_tick_body_exact[
      OF rel roots]])
    fix r t
    assume exact:
      "\<exists>v. r = Result v \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result v) t"
    obtain v where r: "r = Result v"
      and body:
        "one_due_tick_body_post D C branch generic_raw c
          (Result v) t"
      using exact by blast
    note body_facts = body[unfolded one_due_tick_body_post_def]
    note hrs_t = conjunct1[OF body_facts]
    note body_rest1 = conjunct2[OF body_facts]
    note delayed_t = conjunct1[OF body_rest1]
    note body_rest2 = conjunct2[OF body_rest1]
    note top_t = conjunct1[OF body_rest2]
    note body_rest3 = conjunct2[OF body_rest2]
    note tick_t = conjunct1[OF body_rest3]
    note result_pin = conjunct2[OF body_rest3]
    have v_pin:
      "v = (if ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))) = []
        then NULL
        else PTR_COERCE(unit \<rightarrow>
               Scheduler_V611_Parse.tskTaskControlBlock_C)
          (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
              (hd (ring (list_remove_abs
                (one_due_generic_raw_ptr D (odc_task C))
                (generic_raw (odc_delayed_root C))))))))"
      using result_pin by simp
    have selected:
      "(if ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))) = []
        then NULL
        else PTR_COERCE(unit \<rightarrow>
               Scheduler_V611_Parse.tskTaskControlBlock_C)
          (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
              (hd (ring (list_remove_abs
                (one_due_generic_raw_ptr D (odc_task C))
                (generic_raw (odc_delayed_root C)))))))) =
       sd_tcb_ptr D u"
      using nonempty owner_u by simp
    have v_u: "v = sd_tcb_ptr D u"
      by (rule trans[OF v_pin selected])
    have reentry:
      "one_due_gateH_entry_rel D R t a
        (one_due_reentry_context C u) branch'
        (one_due_reentry_snapshot C branch S)
        (one_due_reentry_generic_raw D C
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem
                (Scheduler_V611_Parse.globals.t_hrs_' c))))
          generic_raw)
        (one_due_event_raw_after_remove D C branch event_raw)"
      by (rule one_due_gateH_reentry[OF rel u_live u_raw_member
        head_shape u_due target'_root target'_ne branch'
        hrs_t delayed_t top_t tick_t])
    show
      "r = Result (sd_tcb_ptr D u) \<and>
       one_due_gateH_entry_rel D R t a
        (one_due_reentry_context C u) branch'
        (one_due_reentry_snapshot C branch S)
        (one_due_reentry_generic_raw D C
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem
                (Scheduler_V611_Parse.globals.t_hrs_' c))))
          generic_raw)
        (one_due_event_raw_after_remove D C branch event_raw)"
      using r v_u reentry by simp
  qed
qed

end
