theory Scheduler_Resume_Pending_Control_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drain_Abs_Fold.Scheduler_Resume_Generated_Drain_Abs_Fold"
begin

text \<open>
  The existing pending-drain gate deliberately says nothing about the proof
  port or scheduler-running word.  This independent frame records only that
  those three concrete controls are unchanged.  It can therefore be threaded
  through the old drain proof without imposing the old gate's live-task domain
  on the later cursor-general managed relation.
\<close>

definition resume_pending_control_frame ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "resume_pending_control_frame before after \<longleftrightarrow>
     Scheduler_V611_Parse.globals.eal6_port_critical_depth_' after =
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' before \<and>
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' after =
       Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' before \<and>
     Scheduler_V611_Parse.globals.xSchedulerRunning_' after =
       Scheduler_V611_Parse.globals.xSchedulerRunning_' before"

lemma resume_pending_ready_inserted_control_frame:
  "resume_pending_control_frame c
     (resume_pending_ready_inserted_state D C t generic_raw c)"
  using resume_pending_ready_inserted_globals[
    of D C t generic_raw c]
  by (simp add: resume_pending_control_frame_def)

theorem resume_pending_generated_body_control_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_body (sd_tcb_ptr D t, y) \<bullet> c
     \<lbrace>\<lambda>r s. resume_pending_control_frame c s\<rbrace>"
  apply (rule runs_to_weaken[
    OF resume_pending_generated_body_exact[OF rel tasks roots]])
  by (clarsimp simp: resume_pending_control_frame_def
      resume_pending_ready_inserted_globals split del: if_split)

lemma resume_pending_generated_loop_control_frame_aux:
  fixes ts :: "'tid list"
  shows
    "\<And>c a C S generic_raw event_raw y.
       resume_pending_gate_entry_rel D R c a C S generic_raw
         event_raw \<Longrightarrow>
       rpc_tasks C = ts \<Longrightarrow>
       R = generated_scheduler_roots \<Longrightarrow>
       whileLoop resume_pending_generated_cond
         resume_pending_generated_body
         (resume_pending_next_head_tcb D ts, y) \<bullet> c
       \<lbrace>\<lambda>r s. resume_pending_control_frame c s\<rbrace>"
proof (induction ts)
  case Nil
  have head_null:
    "resume_pending_next_head_tcb D ([] :: 'tid list) = NULL"
    by (simp add: resume_pending_next_head_tcb_def)
  have cond_false:
    "\<not> resume_pending_generated_cond
       (resume_pending_next_head_tcb D ([] :: 'tid list), y) c"
    using head_null
    by (simp add: resume_pending_generated_cond_def)
  show ?case
    apply (subst runs_to_whileLoop_cond_fail
        [of resume_pending_generated_cond
            "(resume_pending_next_head_tcb D ([] :: 'tid list), y)" c,
          OF cond_false])
    by (simp add: resume_pending_control_frame_def)
next
  case (Cons t rest)
  note rel = Cons.prems(1)
  note tasks = Cons.prems(2)
  note roots = Cons.prems(3)
  have head_eq:
    "resume_pending_next_head_tcb D (t # rest) = sd_tcb_ptr D t"
    by (simp add: resume_pending_next_head_tcb_def)
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have live_abs: "t \<in> sa_live a"
    using rel t_live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have guard_t: "c_guard (sd_tcb_ptr D t)"
    using TaskObservationRel_liveD[OF observation live_abs] by blast
  have head_not_null: "sd_tcb_ptr D t \<noteq> NULL"
    by (rule c_guard_NULL[OF guard_t])
  have cond_true:
    "resume_pending_generated_cond (sd_tcb_ptr D t, y) c"
    using head_not_null
    by (simp add: resume_pending_generated_cond_def)
  note body = resume_pending_generated_body_exact[OF rel tasks roots]
  note reentry = resume_pending_gate_reentry[OF rel tasks roots]
  note ctx = resume_pending_drained_context_components[of C t rest]
  show ?case
    apply (simp only: head_eq)
    apply (subst whileLoop_unroll)
    apply (simp only: runs_to_condition_iff)
    apply (simp only: cond_true if_True)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF body])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_weaken[OF Cons.IH[OF reentry _ roots]])
     apply (simp add: ctx)
    by (simp add: resume_pending_control_frame_def
        resume_pending_ready_inserted_globals)
qed

theorem resume_pending_generated_loop_control_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s. resume_pending_control_frame c s\<rbrace>"
  by (rule resume_pending_generated_loop_control_frame_aux[
        OF rel refl roots])

theorem resume_pending_generated_loop_drain_pending_abs_control_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s.
       (\<exists>C' S' gr' er' yw.
          r = Result (NULL, yw) \<and>
          resume_pending_gate_entry_rel D R s
            (drain_pending_abs a) C' S' gr' er' \<and>
          rpc_tasks C' = [] \<and>
          rpc_live C' = rpc_live C \<and>
          rpc_current_priority C' = rpc_current_priority C \<and>
          rpc_priority C' = rpc_priority C \<and>
          ((yw \<noteq> 0) \<longleftrightarrow>
             ((y \<noteq> 0) \<or> resume_pending_requires_yield a))) \<and>
       resume_pending_control_frame c s\<rbrace>"
proof -
  have drain:
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s. \<exists>C' S' gr' er' yw.
        r = Result (NULL, yw) \<and>
        resume_pending_gate_entry_rel D R s
          (drain_pending_abs a) C' S' gr' er' \<and>
        rpc_tasks C' = [] \<and>
        rpc_live C' = rpc_live C \<and>
        rpc_current_priority C' = rpc_current_priority C \<and>
        rpc_priority C' = rpc_priority C \<and>
        ((yw \<noteq> 0) \<longleftrightarrow>
           ((y \<noteq> 0) \<or> resume_pending_requires_yield a))\<rbrace>"
    by (rule resume_pending_generated_loop_drain_pending_abs[OF rel roots])
  have frame:
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s. resume_pending_control_frame c s\<rbrace>"
    by (rule resume_pending_generated_loop_control_frame[OF rel roots])
  show ?thesis using drain frame by (simp only: runs_to_conj)
qed

theorem
  resume_pending_generated_loop_drain_pending_abs_protected_1_1_running_1:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and critical:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 1"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 1"
    and running:
      "Scheduler_V611_Parse.globals.xSchedulerRunning_' c = 1"
  shows
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s.
       (\<exists>C' S' gr' er' yw.
          r = Result (NULL, yw) \<and>
          resume_pending_gate_entry_rel D R s
            (drain_pending_abs a) C' S' gr' er' \<and>
          rpc_tasks C' = [] \<and>
          rpc_live C' = rpc_live C \<and>
          rpc_current_priority C' = rpc_current_priority C \<and>
          rpc_priority C' = rpc_priority C \<and>
          ((yw \<noteq> 0) \<longleftrightarrow>
             ((y \<noteq> 0) \<or> resume_pending_requires_yield a))) \<and>
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' s = 1 \<and>
       Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' s = 1 \<and>
       Scheduler_V611_Parse.globals.xSchedulerRunning_' s = 1\<rbrace>"
  apply (rule runs_to_weaken[
    OF resume_pending_generated_loop_drain_pending_abs_control_frame[
      OF rel roots]])
  using critical interrupts running
  by (auto simp: resume_pending_control_frame_def)

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

  val _ = audit_exact "pending ready-inserted control frame" 0
    @{thm resume_pending_ready_inserted_control_frame}
  val _ = audit_exact "pending generated body control frame" 3
    @{thm resume_pending_generated_body_control_frame}
  val _ = audit_exact "pending generated loop control frame" 2
    @{thm resume_pending_generated_loop_control_frame}
  val _ = audit_exact "pending drain abstract control frame" 2
    @{thm resume_pending_generated_loop_drain_pending_abs_control_frame}
  val _ = audit_exact "pending protected 1/1/running-1 cutpoint" 5
    @{thm
      resume_pending_generated_loop_drain_pending_abs_protected_1_1_running_1}
\<close>

end
