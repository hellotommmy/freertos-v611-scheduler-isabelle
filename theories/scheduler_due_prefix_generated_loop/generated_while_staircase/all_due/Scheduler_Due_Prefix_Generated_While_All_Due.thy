theory Scheduler_Due_Prefix_Generated_While_All_Due
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Last_Due.Scheduler_Due_Prefix_Generated_While_Last_Due"
begin

text \<open>
  Arbitrary finite due-prefix induction for the exact generated while.  No
  length, task identity, priority, tick, pointer, heap address or branch is
  fixed.  Normal body results shorten the symbolic list index; exceptional
  results are reserved for the future-head terminal transition.
\<close>

theorem due_prefix_generated_bare_loop_all_due:
  assumes index:
    "due_prefix_generated_index_inv D R now entry all_due future
       due_tail pxTCB c"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_terminal_post D now entry
       all_due future\<rbrace>"
  using index
proof (induction due_tail arbitrary: pxTCB c)
  case Nil
  obtain processed current C branch S generic_raw event_raw where
      ledger:
        "all_due = processed @ [Generic (odc_task C)]"
    and ptr: "pxTCB = sd_tcb_ptr D (odc_task C)"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
        [Generic (odc_task C)] (map Generic future)
        current C branch S generic_raw event_raw"
    using Nil.prems
    by (auto simp: due_prefix_generated_index_inv_def)
  have terminal:
    "due_prefix_generated_bare_loop (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>due_prefix_generated_terminal_post D now entry
       (processed @ [Generic (odc_task C)]) future\<rbrace>"
    by (rule due_prefix_generated_last_due_bare_loop[OF gate roots])
  show ?case
    using terminal ptr ledger by simp
next
  case (Cons u due_tail)
  have nonnull: "pxTCB \<noteq> NULL"
    by (rule due_prefix_generated_index_inv_nonnull[OF Cons.prems])
  note step = due_prefix_generated_index_result_step[OF Cons.prems roots]
  show ?case
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL) pxTCB c \<Longrightarrow>
       due_prefix_generated_terminal_post D now entry all_due future
         (Result pxTCB) c"
      using nonnull by simp
    show
      "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) pxTCB c \<Longrightarrow>
       one_due_tick_loop_body_source pxTCB \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>due_prefix_generated_terminal_post D now entry
               all_due future\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           due_prefix_generated_terminal_post D now entry
             all_due future (Exn e) t)\<rbrace>"
    proof -
      assume guard: "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) pxTCB c"
      show ?thesis
      proof (rule runs_to_weaken[OF step])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post:
          "(\<forall>q. r = Result q \<longrightarrow>
             due_prefix_generated_index_inv D R now entry all_due future
               due_tail q t) \<and>
           (\<forall>e. r = Exn e \<longrightarrow> False)"
        have recurse:
          "\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>due_prefix_generated_terminal_post D now entry
                 all_due future\<rbrace>"
        proof (intro allI impI)
          fix b
          assume result: "r = Result b"
          have next_index:
            "due_prefix_generated_index_inv D R now entry all_due future
              due_tail b t"
            using post result by blast
          have next_loop:
            "due_prefix_generated_bare_loop b \<bullet> t
             \<lbrace>due_prefix_generated_terminal_post D now entry
               all_due future\<rbrace>"
            by (rule Cons.IH[OF next_index])
          show
            "whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>due_prefix_generated_terminal_post D now entry
               all_due future\<rbrace>"
            using next_loop
            by (simp add: due_prefix_generated_bare_loop_def)
        qed
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>due_prefix_generated_terminal_post D now entry
                 all_due future\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             due_prefix_generated_terminal_post D now entry
               all_due future (Exn e) t)"
          using recurse post by blast
      qed
    qed
  qed
qed

lemma due_prefix_generated_terminal_post_empty_controlD:
  assumes post:
    "due_prefix_generated_terminal_post D now entry all_due [] r t"
  shows "r = Result NULL"
  using post
  by (auto simp: due_prefix_generated_terminal_post_def)

lemma due_prefix_generated_terminal_post_future_controlD:
  assumes post:
    "due_prefix_generated_terminal_post D now entry all_due (f # fs) r t"
  shows "r = Exn ()"
  using post
  by (auto simp: due_prefix_generated_terminal_post_def)

end
