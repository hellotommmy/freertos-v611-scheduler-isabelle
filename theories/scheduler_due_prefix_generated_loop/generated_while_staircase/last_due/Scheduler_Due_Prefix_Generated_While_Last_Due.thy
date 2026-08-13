theory Scheduler_Due_Prefix_Generated_While_Last_Due
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Terminal_Post.Scheduler_Due_Prefix_Generated_While_Terminal_Post"
begin

text \<open>
  The last due task is the control split of the generated loop.  In the empty
  case its body returns NULL and the next guard is false.  In the future case
  its body returns the arbitrary future-head pointer; the next body then throws
  without changing state.  The existential terminal witnesses are supplied
  explicitly so proof search cannot silently select the wrong endpoint.
\<close>

theorem due_prefix_generated_last_due_bare_loop:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (map Generic future)
       current C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>due_prefix_generated_terminal_post D now entry
       (processed @ [Generic (odc_task C)]) future\<rbrace>"
proof (cases future)
  case Nil
  have inv_empty:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] []
       current C branch S generic_raw event_raw"
    using inv Nil by simp
  have head_nonnull: "sd_tcb_ptr D (odc_task C) \<noteq> NULL"
    by (rule due_prefix_gate_inv_head_nonnull[OF inv_empty])
  show ?thesis
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          (sd_tcb_ptr D (odc_task C)) c \<Longrightarrow>
       due_prefix_generated_terminal_post D now entry
         (processed @ [Generic (odc_task C)]) future
         (Result (sd_tcb_ptr D (odc_task C))) c"
      using head_nonnull by simp
    show
      "(\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          (sd_tcb_ptr D (odc_task C)) c \<Longrightarrow>
       one_due_tick_loop_body_source
         (sd_tcb_ptr D (odc_task C)) \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>due_prefix_generated_terminal_post D now entry
               (processed @ [Generic (odc_task C)]) future\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           due_prefix_generated_terminal_post D now entry
             (processed @ [Generic (odc_task C)]) future (Exn e) t)\<rbrace>"
    proof -
      assume guard:
        "(\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          (sd_tcb_ptr D (odc_task C)) c"
      note body = due_prefix_generated_last_due_empty_body[
        OF inv_empty roots]
      show ?thesis
      proof (rule runs_to_weaken[OF body])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post:
          "r = Result NULL \<and>
           one_due_tick_body_post D C branch generic_raw c
             (Result NULL) t \<and>
           due_prefix_exit_inv now entry
             (processed @ [Generic (odc_task C)]) [] []
             (due_prefix_result_step_abs entry processed
               (Generic (odc_task C))) EmptyExit None \<and>
           due_prefix_terminal_source_rel D []
             (due_prefix_result_step_abs entry processed
               (Generic (odc_task C))) EmptyExit None NULL"
        have endpoint:
          "due_prefix_generated_terminal_post D now entry
             (processed @ [Generic (odc_task C)]) future
             (Result NULL) t"
          unfolding due_prefix_generated_terminal_post_def
          apply (rule exI[where x =
            "due_prefix_result_step_abs entry processed
              (Generic (odc_task C))"])
          apply (rule exI[where x = EmptyExit])
          apply (rule exI[where x = None])
          apply (rule exI[where x =
            "NULL :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr"])
          apply (rule exI[where x = C])
          apply (rule exI[where x = branch])
          apply (rule exI[where x = generic_raw])
          apply (rule exI[where x = c])
          using post Nil by simp
        have loop_null:
          "whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source NULL \<bullet> t
           \<lbrace>due_prefix_generated_terminal_post D now entry
             (processed @ [Generic (odc_task C)]) future\<rbrace>"
          apply (subst runs_to_whileLoop_cond_fail)
           apply simp
          apply runs_to_vcg
          by (rule endpoint)
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>due_prefix_generated_terminal_post D now entry
                 (processed @ [Generic (odc_task C)]) future\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic (odc_task C)]) future (Exn e) t)"
          using post loop_null by auto
      qed
    qed
  qed
next
  case (Cons f fs)
  have inv_future:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # map Generic fs)
       current C branch S generic_raw event_raw"
    using inv Cons by simp
  have head_nonnull: "sd_tcb_ptr D (odc_task C) \<noteq> NULL"
    by (rule due_prefix_gate_inv_head_nonnull[OF inv_future])
  show ?thesis
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          (sd_tcb_ptr D (odc_task C)) c \<Longrightarrow>
       due_prefix_generated_terminal_post D now entry
         (processed @ [Generic (odc_task C)]) future
         (Result (sd_tcb_ptr D (odc_task C))) c"
      using head_nonnull by simp
    show
      "(\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          (sd_tcb_ptr D (odc_task C)) c \<Longrightarrow>
       one_due_tick_loop_body_source
         (sd_tcb_ptr D (odc_task C)) \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>due_prefix_generated_terminal_post D now entry
               (processed @ [Generic (odc_task C)]) future\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           due_prefix_generated_terminal_post D now entry
             (processed @ [Generic (odc_task C)]) future (Exn e) t)\<rbrace>"
    proof -
      assume guard:
        "(\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          (sd_tcb_ptr D (odc_task C)) c"
      note body = due_prefix_generated_last_due_future_body[
        OF inv_future roots]
      show ?thesis
      proof (rule runs_to_weaken[OF body])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post:
          "r = Result (sd_tcb_ptr D f) \<and>
           one_due_tick_body_post D C branch generic_raw c
             (Result (sd_tcb_ptr D f)) t \<and>
           due_prefix_exit_inv now entry
             (processed @ [Generic (odc_task C)]) []
             (Generic f # map Generic fs)
             (due_prefix_result_step_abs entry processed
               (Generic (odc_task C))) FutureExit (Some (Generic f)) \<and>
           due_prefix_terminal_source_rel D (Generic f # map Generic fs)
             (due_prefix_result_step_abs entry processed
               (Generic (odc_task C))) FutureExit (Some (Generic f))
             (sd_tcb_ptr D f) \<and>
           (\<exists>k. due_prefix_future_source_ready D t now
             (due_prefix_result_step_abs entry processed
               (Generic (odc_task C))) f k)"
        obtain k where ready:
          "due_prefix_future_source_ready D t now
            (due_prefix_result_step_abs entry processed
              (Generic (odc_task C))) f k"
          using post by blast
        have f_nonnull: "sd_tcb_ptr D f \<noteq> NULL"
          by (rule due_prefix_future_source_ready_nonnull[OF ready])
        have throws:
          "one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
           \<lbrace>\<lambda>q u. q = Exn () \<and> u = t\<rbrace>"
          by (rule due_prefix_future_source_ready_throws[OF ready])
        have endpoint:
          "due_prefix_generated_terminal_post D now entry
             (processed @ [Generic (odc_task C)]) future (Exn ()) t"
          unfolding due_prefix_generated_terminal_post_def
          apply (rule exI[where x =
            "due_prefix_result_step_abs entry processed
              (Generic (odc_task C))"])
          apply (rule exI[where x = FutureExit])
          apply (rule exI[where x = "Some (Generic f)"])
          apply (rule exI[where x = "sd_tcb_ptr D f"])
          apply (rule exI[where x = C])
          apply (rule exI[where x = branch])
          apply (rule exI[where x = generic_raw])
          apply (rule exI[where x = c])
          using post Cons by simp
        have loop_future:
          "whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
           \<lbrace>due_prefix_generated_terminal_post D now entry
             (processed @ [Generic (odc_task C)]) future\<rbrace>"
        proof (rule runs_to_whileLoop_unroll_exn)
          show
            "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
                (sd_tcb_ptr D f) t \<Longrightarrow>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic (odc_task C)]) future
               (Result (sd_tcb_ptr D f)) t"
            using f_nonnull by simp
          show
            "(\<lambda>pxTCB _. pxTCB \<noteq> NULL)
                (sd_tcb_ptr D f) t \<Longrightarrow>
             one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
             \<lbrace>\<lambda>q u.
               (\<forall>b. q = Result b \<longrightarrow>
                 whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
                   one_due_tick_loop_body_source b \<bullet> u
                   \<lbrace>due_prefix_generated_terminal_post D now entry
                     (processed @ [Generic (odc_task C)]) future\<rbrace>) \<and>
               (\<forall>e. q = Exn e \<longrightarrow>
                 due_prefix_generated_terminal_post D now entry
                   (processed @ [Generic (odc_task C)]) future
                   (Exn e) u)\<rbrace>"
          proof -
            assume guard_f:
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
                     \<lbrace>due_prefix_generated_terminal_post D now entry
                       (processed @ [Generic (odc_task C)]) future\<rbrace>) \<and>
                 (\<forall>e. q = Exn e \<longrightarrow>
                   due_prefix_generated_terminal_post D now entry
                     (processed @ [Generic (odc_task C)]) future
                     (Exn e) u)"
                using throw_post endpoint by auto
            qed
          qed
        qed
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>due_prefix_generated_terminal_post D now entry
                 (processed @ [Generic (odc_task C)]) future\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic (odc_task C)]) future (Exn e) t)"
          using post loop_future by auto
      qed
    qed
  qed
qed

end
