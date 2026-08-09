theory Scheduler_Due_Prefix_Strong_Terminal_Future_Source
  imports Scheduler_Due_Prefix_Strong_Terminal_Future_State
begin

definition DueLoopStrongTerminalFutureBodyPost ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "DueLoopStrongTerminalFutureBodyPost D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       before r t \<longleftrightarrow>
     r = Result (sd_tcb_ptr D f) \<and>
     one_due_tick_body_post D C branch generic_raw before
       (Result (sd_tcb_ptr D f)) t \<and>
     due_prefix_terminal_source_rel D (Generic f # map Generic fs)
       (due_prefix_result_step_abs entry processed (Generic task))
       FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
     DueLoopStrongTerminalFutureState D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       before t"

theorem DueLoopStrongHeadRel_last_future_result_full:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed [Generic task]
       (Generic f # map Generic fs) phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed [Generic task]
         (Generic f # map Generic fs) current
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>DueLoopStrongTerminalFutureBodyPost D now entry processed task f fs
        C branch S generic_raw event_raw K_G K_E managed termination external
        c\<rbrace>"
proof -
  have gate_C:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # map Generic fs) current
       C branch S generic_raw event_raw"
    using gate selector by simp
  note source_C = due_prefix_generated_last_due_future_body[
    OF gate_C roots]
  have local:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  note exact_state = one_due_tick_body_state_exact[OF local roots]
  have source_task:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (sd_tcb_ptr D f) \<and>
       one_due_tick_body_post D C branch generic_raw c
         (Result (sd_tcb_ptr D f)) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic task]) []
         (Generic f # map Generic fs)
         (due_prefix_result_step_abs entry processed (Generic task))
         FutureExit (Some (Generic f)) \<and>
       due_prefix_terminal_source_rel D
         (Generic f # map Generic fs)
         (due_prefix_result_step_abs entry processed (Generic task))
         FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
       (\<exists>k. due_prefix_future_source_ready D t now
         (due_prefix_result_step_abs entry processed (Generic task)) f k)\<rbrace>"
    using source_C selector by simp
  have exact_state_task:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t. t = one_due_tick_ready_inserted_state
       D C branch generic_raw c\<rbrace>"
    using exact_state selector by simp
  have source:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       (r = Result (sd_tcb_ptr D f) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic task]) []
          (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed
            (Generic task))
          FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D
          (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed
            (Generic task))
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
        (\<exists>k. due_prefix_future_source_ready D t now
          (due_prefix_result_step_abs entry processed
            (Generic task)) f k)) \<and>
       t = one_due_tick_ready_inserted_state
         D C branch generic_raw c\<rbrace>"
    using source_task exact_state_task by (simp only: runs_to_conj)
  have strong_state:
    "DueLoopStrongTerminalFutureState D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       c (one_due_tick_ready_inserted_state D C branch generic_raw c)"
    by (rule DueLoopStrongHeadRel_last_future_result_full_state[
          OF strong gate selector roots])
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "(r = Result (sd_tcb_ptr D f) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic task]) []
          (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed
            (Generic task))
          FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D
          (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed
            (Generic task))
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
        (\<exists>k. due_prefix_future_source_ready D t now
          (due_prefix_result_step_abs entry processed
             (Generic task)) f k)) \<and>
       t = one_due_tick_ready_inserted_state D C branch generic_raw c"
    note post_left = conjunct1[OF post]
    note state_eq = conjunct2[OF post]
    note r_eq = conjunct1[OF post_left]
    note post_tail1 = conjunct2[OF post_left]
    note body_post = conjunct1[OF post_tail1]
    note post_tail2 = conjunct2[OF post_tail1]
    note exit_post = conjunct1[OF post_tail2]
    note post_tail3 = conjunct2[OF post_tail2]
    note terminal_rel = conjunct1[OF post_tail3]
    note future_ready = conjunct2[OF post_tail3]
    have state:
      "DueLoopStrongTerminalFutureState D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c t"
      using strong_state state_eq by simp
    show
      "DueLoopStrongTerminalFutureBodyPost D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c r t"
      unfolding DueLoopStrongTerminalFutureBodyPost_def
      using r_eq body_post exit_post terminal_rel future_ready state by simp
  qed
qed

text \<open>
  Exact generated exception trace.  The first body is the last due step and
  returns the arbitrary future-head pointer.  The next guard is true; that
  future body throws before its first write.  Consequently the bare loop
  exposes Exn and the complete generated state remains the last-due poststate.
  The legacy terminal post is retained in the same run so later lifting does
  not need a determinism argument to merge weak and strong executions.
\<close>

theorem DueLoopStrongHeadRel_last_future_bare_loop_full:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed [Generic task]
       (Generic f # map Generic fs) phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed [Generic task]
         (Generic f # map Generic fs) current
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Exn () \<and>
       DueLoopStrongTerminalFutureState D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c t \<and>
       due_prefix_generated_terminal_post D now entry
         (processed @ [Generic task]) (f # fs) (Exn ()) t\<rbrace>"
proof -
  have head_nonnull: "sd_tcb_ptr D task \<noteq> NULL"
    using due_prefix_gate_inv_head_nonnull[OF gate] selector by simp
  note body = DueLoopStrongHeadRel_last_future_result_full[
    OF strong gate selector roots]
  show ?thesis
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D task) c \<Longrightarrow>
       (Result (sd_tcb_ptr D task) = Exn () \<and>
        DueLoopStrongTerminalFutureState D now entry processed task f fs C
          branch S generic_raw event_raw K_G K_E managed termination external
          c c \<and>
        due_prefix_generated_terminal_post D now entry
          (processed @ [Generic task]) (f # fs) (Exn ()) c)"
      using head_nonnull by simp
    show
      "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D task) c \<Longrightarrow>
       one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>\<lambda>q u.
               q = Exn () \<and>
               DueLoopStrongTerminalFutureState D now entry processed
                 task f fs C branch S generic_raw event_raw K_G K_E
                 managed termination external c u \<and>
               due_prefix_generated_terminal_post D now entry
                 (processed @ [Generic task]) (f # fs) (Exn ()) u\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           Exn e = Exn () \<and>
           DueLoopStrongTerminalFutureState D now entry processed
             task f fs C branch S generic_raw event_raw K_G K_E
             managed termination external c t \<and>
           due_prefix_generated_terminal_post D now entry
             (processed @ [Generic task]) (f # fs) (Exn ()) t)\<rbrace>"
    proof -
      assume guard:
        "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D task) c"
      show ?thesis
      proof (rule runs_to_weaken[OF body])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume body_post:
          "DueLoopStrongTerminalFutureBodyPost D now entry processed
             task f fs C branch S generic_raw event_raw K_G K_E
             managed termination external c r t"
        have result: "r = Result (sd_tcb_ptr D f)"
          and body_exact:
            "one_due_tick_body_post D C branch generic_raw c
              (Result (sd_tcb_ptr D f)) t"
          and terminal_source:
            "due_prefix_terminal_source_rel D
              (Generic f # map Generic fs)
              (due_prefix_result_step_abs entry processed (Generic task))
              FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
          and state:
            "DueLoopStrongTerminalFutureState D now entry processed
              task f fs C branch S generic_raw event_raw K_G K_E
              managed termination external c t"
          using body_post
          by (simp_all add: DueLoopStrongTerminalFutureBodyPost_def)
        let ?after =
          "due_prefix_result_step_abs entry processed (Generic task)"
        let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
        let ?hg = "one_due_generic_remove_heap D C ?h0"
        let ?he = "one_due_event_remove_heap D C branch ?hg"
        let ?generic_raw' =
          "one_due_reentry_generic_raw D C ?he generic_raw"
        let ?event_raw' =
          "one_due_event_raw_after_remove D C branch event_raw"
        let ?S' = "one_due_reentry_snapshot C branch S"
        note state_facts =
          state[unfolded DueLoopStrongTerminalFutureState_def Let_def]
        note state_eq = conjunct1[OF state_facts]
        note state_tail = conjunct2[OF state_facts]
        have terminal_head:
          "StrongDuePrefixLoopHeadRel D t ?after managed termination external
             ?generic_raw' (ods_generic_family ?S')
             ?event_raw' (ods_event_family ?S') K_G K_E ?S'
             now entry (processed @ [Generic task]) []
              (Generic f # map Generic fs)
              FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
          by (rule conjunct1[OF state_tail])
        have exit:
          "due_prefix_exit_inv now entry (processed @ [Generic task]) []
             (Generic f # map Generic fs) ?after
             FutureExit (Some (Generic f))"
          by (rule StrongDuePrefixLoopHeadRel_exitD[OF terminal_head])
        have ready:
          "due_prefix_future_source_ready D t now ?after f (K_G f)"
          by (rule conjunct2[OF state_tail])
        have f_nonnull: "sd_tcb_ptr D f \<noteq> NULL"
          by (rule due_prefix_future_source_ready_nonnull[OF ready])
        have throws:
          "one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
           \<lbrace>\<lambda>q u. q = Exn () \<and> u = t\<rbrace>"
          by (rule due_prefix_future_source_ready_throws[OF ready])
        have legacy_terminal:
          "due_prefix_generated_terminal_post D now entry
             (processed @ [Generic task]) (f # fs) (Exn ()) t"
          unfolding due_prefix_generated_terminal_post_def
          apply (rule exI[where x = "?after"])
          apply (rule exI[where x=FutureExit])
          apply (rule exI[where x="Some (Generic f)"])
          apply (rule exI[where x="sd_tcb_ptr D f"])
          apply (rule exI[where x=C])
          apply (rule exI[where x=branch])
          apply (rule exI[where x=generic_raw])
          apply (rule exI[where x=c])
          using exit terminal_source body_exact by simp
        have loop_future:
          "whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
           \<lbrace>\<lambda>q u.
             q = Exn () \<and>
             DueLoopStrongTerminalFutureState D now entry processed
               task f fs C branch S generic_raw event_raw K_G K_E
               managed termination external c u \<and>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic task]) (f # fs) (Exn ()) u\<rbrace>"
        proof (rule runs_to_whileLoop_unroll_exn)
          show
            "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D f) t \<Longrightarrow>
             Result (sd_tcb_ptr D f) = Exn () \<and>
             DueLoopStrongTerminalFutureState D now entry processed
               task f fs C branch S generic_raw event_raw K_G K_E
               managed termination external c t \<and>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic task]) (f # fs) (Exn ()) t"
            using f_nonnull by simp
          show
            "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D f) t \<Longrightarrow>
             one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
             \<lbrace>\<lambda>q u.
               (\<forall>b. q = Result b \<longrightarrow>
                 whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
                   one_due_tick_loop_body_source b \<bullet> u
                   \<lbrace>\<lambda>v w.
                     v = Exn () \<and>
                     DueLoopStrongTerminalFutureState D now entry processed
                       task f fs C branch S generic_raw event_raw K_G K_E
                       managed termination external c w \<and>
                     due_prefix_generated_terminal_post D now entry
                       (processed @ [Generic task]) (f # fs)
                       (Exn ()) w\<rbrace>) \<and>
               (\<forall>e. q = Exn e \<longrightarrow>
                 Exn e = Exn () \<and>
                 DueLoopStrongTerminalFutureState D now entry processed
                   task f fs C branch S generic_raw event_raw K_G K_E
                   managed termination external c u \<and>
                 due_prefix_generated_terminal_post D now entry
                   (processed @ [Generic task]) (f # fs) (Exn ()) u)\<rbrace>"
          proof -
            assume future_guard:
              "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D f) t"
            show ?thesis
            proof (rule runs_to_weaken[OF throws])
              fix q ::
                "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
              fix u :: Scheduler_V611_Parse.globals
              assume throw_post: "q = Exn () \<and> u = t"
              show
                "(\<forall>b. q = Result b \<longrightarrow>
                   whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
                     one_due_tick_loop_body_source b \<bullet> u
                     \<lbrace>\<lambda>v w.
                       v = Exn () \<and>
                       DueLoopStrongTerminalFutureState D now entry processed
                         task f fs C branch S generic_raw event_raw K_G K_E
                         managed termination external c w \<and>
                       due_prefix_generated_terminal_post D now entry
                         (processed @ [Generic task]) (f # fs)
                         (Exn ()) w\<rbrace>) \<and>
                 (\<forall>e. q = Exn e \<longrightarrow>
                   Exn e = Exn () \<and>
                   DueLoopStrongTerminalFutureState D now entry processed
                     task f fs C branch S generic_raw event_raw K_G K_E
                     managed termination external c u \<and>
                   due_prefix_generated_terminal_post D now entry
                     (processed @ [Generic task]) (f # fs) (Exn ()) u)"
                using throw_post state legacy_terminal by auto
            qed
          qed
        qed
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>\<lambda>q u.
                 q = Exn () \<and>
                 DueLoopStrongTerminalFutureState D now entry processed
                   task f fs C branch S generic_raw event_raw K_G K_E
                   managed termination external c u \<and>
                 due_prefix_generated_terminal_post D now entry
                   (processed @ [Generic task]) (f # fs) (Exn ()) u\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             Exn e = Exn () \<and>
             DueLoopStrongTerminalFutureState D now entry processed
               task f fs C branch S generic_raw event_raw K_G K_E
               managed termination external c t \<and>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic task]) (f # fs) (Exn ()) t)"
          using result loop_future by auto
      qed
    qed
  qed
qed

theorem DueLoopStrongHeadRel_last_future_finally_full:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed [Generic task]
       (Generic f # map Generic fs) phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed [Generic task]
         (Generic f # map Generic fs) current
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       DueLoopStrongTerminalFutureState D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c t \<and>
       due_prefix_generated_public_post D now entry
         (processed @ [Generic task]) (f # fs) t\<rbrace>"
proof -
  note bare = DueLoopStrongHeadRel_last_future_bare_loop_full[
    OF strong gate selector roots]
  have bare_public:
    "due_prefix_generated_bare_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>_ t.
       DueLoopStrongTerminalFutureState D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c t \<and>
       due_prefix_generated_public_post D now entry
         (processed @ [Generic task]) (f # fs) t\<rbrace>"
  proof (rule runs_to_weaken[OF bare])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Exn () \<and>
       DueLoopStrongTerminalFutureState D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c t \<and>
       due_prefix_generated_terminal_post D now entry
         (processed @ [Generic task]) (f # fs) (Exn ()) t"
    have public:
      "due_prefix_generated_public_post D now entry
         (processed @ [Generic task]) (f # fs) t"
      unfolding due_prefix_generated_public_post_def
      apply (rule exI[where x="Exn ()"])
      using post by simp
    show
      "DueLoopStrongTerminalFutureState D now entry processed task f fs C
         branch S generic_raw event_raw K_G K_E managed termination external
         c t \<and>
       due_prefix_generated_public_post D now entry
         (processed @ [Generic task]) (f # fs) t"
      using post public by simp
  qed
  show ?thesis
    by (rule due_prefix_generated_finally_normalises[OF bare_public])
qed

end
