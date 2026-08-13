theory Scheduler_Due_Prefix_Terminal_Future_Ready
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Defs.Scheduler_Due_Prefix_Terminal_Defs"
begin

lemma due_prefix_future_source_ready_obsD:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows
    "TaskObservationRel D
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
proof -
  have facts:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a \<and>
     f \<in> sa_live a \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = now \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = k \<and>
     now < k"
    by (rule due_prefix_future_source_ready_def[THEN iffD1, OF ready])
  show ?thesis by (rule conjunct1[OF facts])
qed

lemma due_prefix_future_source_ready_liveD:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows "f \<in> sa_live a"
proof -
  have facts:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a \<and>
     f \<in> sa_live a \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = now \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = k \<and>
     now < k"
    by (rule due_prefix_future_source_ready_def[THEN iffD1, OF ready])
  show ?thesis by (rule conjunct1[OF conjunct2[OF facts]])
qed

lemma due_prefix_future_source_ready_tickD:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows "Scheduler_V611_Parse.globals.xTickCount_' c = now"
proof -
  have facts:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a \<and>
     f \<in> sa_live a \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = now \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = k \<and>
     now < k"
    by (rule due_prefix_future_source_ready_def[THEN iffD1, OF ready])
  show ?thesis
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF facts]]])
qed

lemma due_prefix_future_source_ready_keyD:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
      (one_due_generic_raw_ptr D f) = k"
proof -
  have facts:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a \<and>
     f \<in> sa_live a \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = now \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = k \<and>
     now < k"
    by (rule due_prefix_future_source_ready_def[THEN iffD1, OF ready])
  show ?thesis
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF facts]]]])
qed

lemma due_prefix_future_source_ready_futureD:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows "now < k"
proof -
  have facts:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a \<and>
     f \<in> sa_live a \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = now \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = k \<and>
     now < k"
    by (rule due_prefix_future_source_ready_def[THEN iffD1, OF ready])
  show ?thesis
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF facts]]]])
qed

lemma due_prefix_future_source_ready_throws:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> c
     \<lbrace>\<lambda>r t. r = Exn () \<and> t = c\<rbrace>"
proof -
  note obs = due_prefix_future_source_ready_obsD[OF ready]
  note live = due_prefix_future_source_ready_liveD[OF ready]
  note tick = due_prefix_future_source_ready_tickD[OF ready]
  note key = due_prefix_future_source_ready_keyD[OF ready]
  note future = due_prefix_future_source_ready_futureD[OF ready]
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?tp = "sd_tcb_ptr D f"
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
