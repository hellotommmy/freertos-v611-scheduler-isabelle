theory Scheduler_Due_Prefix_Generated_While_Zero
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_All_Due.Scheduler_Due_Prefix_Generated_While_All_Due"
begin

text \<open>
  Zero due tasks is a genuine symbolic branch, not a fixed-value shortcut.
  Its arbitrary future list determines the initial pointer and exact control:
  empty future yields Result NULL immediately; nonempty future executes its
  arbitrary head and yields Exn () without a state change.
\<close>

definition due_prefix_generated_zero_terminal_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_zero_terminal_post D now entry future before r t
       \<longleftrightarrow>
     t = before \<and>
     (\<exists>phase next v.
        due_prefix_exit_inv now entry [] [] (map Generic future)
          entry phase next \<and>
        due_prefix_terminal_source_rel D (map Generic future)
          entry phase next v \<and>
        ((future = [] \<and> r = Result NULL) \<or>
         (future \<noteq> [] \<and> r = Exn ())))"

theorem due_prefix_generated_zero_due_empty_bare_loop:
  assumes exit:
    "due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
  shows
    "due_prefix_generated_bare_loop NULL \<bullet> c
     \<lbrace>due_prefix_generated_zero_terminal_post D now entry [] c\<rbrace>"
  unfolding due_prefix_generated_bare_loop_def
  apply (subst runs_to_whileLoop_cond_fail)
   apply simp
  apply runs_to_vcg
  unfolding due_prefix_generated_zero_terminal_post_def
  apply (rule conjI)
   apply simp
  apply (rule exI[where x = EmptyExit])
  apply (rule exI[where x = None])
  apply (rule exI[where x =
    "NULL :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr"])
  using exit
  by (simp add: due_prefix_terminal_source_rel_def
      due_prefix_bare_terminal_rel_def)

theorem due_prefix_generated_zero_due_future_bare_loop:
  assumes exit:
    "due_prefix_exit_inv now entry [] []
       (Generic f # map Generic fs) entry FutureExit (Some (Generic f))"
    and ready: "due_prefix_future_source_ready D c now entry f k"
  shows
    "due_prefix_generated_bare_loop (sd_tcb_ptr D f) \<bullet> c
     \<lbrace>due_prefix_generated_zero_terminal_post D now entry
       (f # fs) c\<rbrace>"
proof -
  have nonnull: "sd_tcb_ptr D f \<noteq> NULL"
    by (rule due_prefix_future_source_ready_nonnull[OF ready])
  have throws:
    "one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> c
     \<lbrace>\<lambda>r t. r = Exn () \<and> t = c\<rbrace>"
    by (rule due_prefix_future_source_ready_throws[OF ready])
  have endpoint:
    "due_prefix_generated_zero_terminal_post D now entry (f # fs) c
       (Exn ()) c"
    unfolding due_prefix_generated_zero_terminal_post_def
    apply (rule conjI)
     apply simp
    apply (rule exI[where x = FutureExit])
    apply (rule exI[where x = "Some (Generic f)"])
    apply (rule exI[where x = "sd_tcb_ptr D f"])
    using exit
    by (simp add: due_prefix_terminal_source_rel_def
        due_prefix_bare_terminal_rel_def)
  show ?thesis
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D f) c
       \<Longrightarrow>
       due_prefix_generated_zero_terminal_post D now entry (f # fs) c
         (Result (sd_tcb_ptr D f)) c"
      using nonnull by simp
    show
      "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D f) c
       \<Longrightarrow>
       one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>due_prefix_generated_zero_terminal_post D now entry
               (f # fs) c\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           due_prefix_generated_zero_terminal_post D now entry
             (f # fs) c (Exn e) t)\<rbrace>"
    proof -
      assume guard:
        "(\<lambda>pxTCB _. pxTCB \<noteq> NULL) (sd_tcb_ptr D f) c"
      show ?thesis
      proof (rule runs_to_weaken[OF throws])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post: "r = Exn () \<and> t = c"
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>due_prefix_generated_zero_terminal_post D now entry
                 (f # fs) c\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             due_prefix_generated_zero_terminal_post D now entry
               (f # fs) c (Exn e) t)"
          using post endpoint by auto
      qed
    qed
  qed
qed

lemma due_prefix_generated_zero_terminal_post_empty_controlD:
  assumes post:
    "due_prefix_generated_zero_terminal_post D now entry [] before r t"
  shows "r = Result NULL \<and> t = before"
  using post
  by (auto simp: due_prefix_generated_zero_terminal_post_def)

lemma due_prefix_generated_zero_terminal_post_future_controlD:
  assumes post:
    "due_prefix_generated_zero_terminal_post D now entry
       (f # fs) before r t"
  shows "r = Exn () \<and> t = before"
  using post
  by (auto simp: due_prefix_generated_zero_terminal_post_def)

theorem due_prefix_generated_zero_due_bare_loop:
  assumes empty:
    "future = [] \<Longrightarrow>
       pxTCB = NULL \<and>
       due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
    and nonempty:
      "\<And>f fs. future = f # fs \<Longrightarrow>
        \<exists>k. pxTCB = sd_tcb_ptr D f \<and>
          due_prefix_exit_inv now entry [] []
            (Generic f # map Generic fs) entry
            FutureExit (Some (Generic f)) \<and>
          due_prefix_future_source_ready D c now entry f k"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_zero_terminal_post D now entry
       future c\<rbrace>"
proof (cases future)
  case Nil
  have ptr: "pxTCB = NULL"
    and exit:
      "due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
    using empty[OF Nil] by blast+
  note terminal = due_prefix_generated_zero_due_empty_bare_loop[
    where D=D and c=c, OF exit]
  show ?thesis
    using terminal ptr Nil by simp
next
  case (Cons f fs)
  obtain k where ptr: "pxTCB = sd_tcb_ptr D f"
    and exit:
      "due_prefix_exit_inv now entry [] []
        (Generic f # map Generic fs) entry
        FutureExit (Some (Generic f))"
    and ready: "due_prefix_future_source_ready D c now entry f k"
    using nonempty[OF Cons] by blast
  note terminal = due_prefix_generated_zero_due_future_bare_loop[
    OF exit ready]
  show ?thesis
    using terminal ptr Cons by simp
qed

end
