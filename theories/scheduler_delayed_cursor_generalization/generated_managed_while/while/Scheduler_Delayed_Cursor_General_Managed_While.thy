theory Scheduler_Delayed_Cursor_General_Managed_While
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter.Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter"
begin

text \<open>
  Arbitrary finite nonempty execution.  Induction is on the exact tail after
  the current due task.  Nil uses only the cursor-general terminal adapter;
  Cons uses only the cursor-general non-last index step.  Exceptional future
  exits are terminal and never converted to successor indices.
\<close>

theorem cursor_general_due_prefix_managed_generated_bare_loop_nonempty:
  assumes index:
    "cursor_general_due_prefix_managed_generated_head_index D R now entry
       all_due future processed task due_tail pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post D now
       entry all_due future managed termination external K_G K_E\<rbrace>"
  using index
proof (induction due_tail arbitrary: processed task pxTCB c)
  case Nil
  show ?case
    by (rule cursor_general_due_prefix_managed_generated_last_index_bare[
          OF Nil.prems roots])
next
  case (Cons u due_tail)
  have nonnull: "pxTCB \<noteq> NULL"
    by (rule
      cursor_general_due_prefix_managed_generated_head_index_nonnull[
        OF Cons.prems])
  note step =
    cursor_general_due_prefix_managed_generated_nonlast_index_step[
      OF Cons.prems roots]
  show ?case
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>p _. p \<noteq> NULL) pxTCB c \<Longrightarrow>
       cursor_general_due_prefix_managed_generated_terminal_post D now entry
         all_due future managed termination external K_G K_E
         (Result pxTCB) c"
      using nonnull by simp
    show
      "(\<lambda>p _. p \<noteq> NULL) pxTCB c \<Longrightarrow>
       one_due_tick_loop_body_source pxTCB \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post
               D now entry all_due future managed termination external
               K_G K_E\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           cursor_general_due_prefix_managed_generated_terminal_post D now
             entry all_due future managed termination external K_G K_E
             (Exn e) t)\<rbrace>"
    proof -
      assume guard: "(\<lambda>p _. p \<noteq> NULL) pxTCB c"
      show ?thesis
      proof (rule runs_to_weaken[OF step])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post:
          "r = Result (sd_tcb_ptr D u) \<and>
           cursor_general_due_prefix_managed_generated_head_index D R now
             entry all_due future (processed @ [Generic task]) u due_tail
             (sd_tcb_ptr D u) t managed termination external K_G K_E"
        have result: "r = Result (sd_tcb_ptr D u)"
          using post by simp
        have next_index:
          "cursor_general_due_prefix_managed_generated_head_index D R now
            entry all_due future (processed @ [Generic task]) u due_tail
            (sd_tcb_ptr D u) t managed termination external K_G K_E"
          using post by simp
        have next_loop:
          "due_prefix_generated_bare_loop (sd_tcb_ptr D u) \<bullet> t
           \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post
             D now entry all_due future managed termination external
             K_G K_E\<rbrace>"
          by (rule Cons.IH[OF next_index])
        have recurse:
          "whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source (sd_tcb_ptr D u) \<bullet> t
           \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post
             D now entry all_due future managed termination external
             K_G K_E\<rbrace>"
          using next_loop by (simp add: due_prefix_generated_bare_loop_def)
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>p _. p \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post
                 D now entry all_due future managed termination external
                 K_G K_E\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             cursor_general_due_prefix_managed_generated_terminal_post D now
               entry all_due future managed termination external K_G K_E
               (Exn e) t)"
          using result recurse by auto
      qed
    qed
  qed
qed

theorem cursor_general_due_prefix_managed_generated_finally_loop_nonempty:
  assumes index:
    "cursor_general_due_prefix_managed_generated_head_index D R now entry
       all_due future processed task due_tail pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       (\<exists>q. cursor_general_due_prefix_managed_generated_terminal_post
         D now entry all_due future managed termination external K_G K_E
         q t)\<rbrace>"
proof -
  have bare:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post D now
       entry all_due future managed termination external K_G K_E\<rbrace>"
    by (rule cursor_general_due_prefix_managed_generated_bare_loop_nonempty[
          OF index roots])
  have bare_public:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>_ t. \<exists>q.
       cursor_general_due_prefix_managed_generated_terminal_post D now entry
         all_due future managed termination external K_G K_E q t\<rbrace>"
  proof (rule runs_to_weaken[OF bare])
    fix q ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "cursor_general_due_prefix_managed_generated_terminal_post D now entry
         all_due future managed termination external K_G K_E q t"
    show
      "\<exists>q. cursor_general_due_prefix_managed_generated_terminal_post
         D now entry all_due future managed termination external K_G K_E q t"
      by (rule exI[where x=q], rule post)
  qed
  show ?thesis
    by (rule due_prefix_generated_finally_normalises[OF bare_public])
qed

end
