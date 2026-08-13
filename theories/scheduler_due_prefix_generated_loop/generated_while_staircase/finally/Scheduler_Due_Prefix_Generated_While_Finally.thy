theory Scheduler_Due_Prefix_Generated_While_Finally
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Complete.Scheduler_Due_Prefix_Generated_While_Complete"
begin

definition due_prefix_generated_public_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid list \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_public_post D now entry all_due future t
       \<longleftrightarrow>
     (\<exists>r. due_prefix_generated_terminal_post D now entry
       all_due future r t)"

definition due_prefix_generated_zero_public_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_zero_public_post D now entry future before t
       \<longleftrightarrow>
     (\<exists>r. due_prefix_generated_zero_terminal_post D now entry
       future before r t)"

definition due_prefix_generated_complete_public_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_complete_public_post D now entry due_tasks future
       before t \<longleftrightarrow>
     (\<exists>r. due_prefix_generated_complete_terminal_post D now entry
       due_tasks future before r t)"

text \<open>
  The CParser finally combinator maps both inner Result () and inner Exn () to
  the same public Result ().  Binding the pointer-valued bare loop to skip is
  essential: it makes the normal and exceptional payload types both unit before
  applying finally.
\<close>

lemma due_prefix_generated_finally_normalises:
  assumes bare:
    "due_prefix_generated_bare_loop pxTCB \<bullet> s
     \<lbrace>\<lambda>_ t. Q t\<rbrace>"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and> Q t\<rbrace>"
  unfolding due_prefix_generated_finally_loop_def
  apply runs_to_vcg
  apply (rule runs_to_weaken[OF bare])
  by auto

theorem due_prefix_generated_finally_loop_all_due:
  assumes index:
    "due_prefix_generated_index_inv D R now entry all_due future
       due_tail pxTCB c"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_generated_public_post D now entry all_due future t\<rbrace>"
proof -
  have bare:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_terminal_post D now entry
       all_due future\<rbrace>"
    by (rule due_prefix_generated_bare_loop_all_due[OF index roots])
  have bare_public:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>_ t.
       due_prefix_generated_public_post D now entry all_due future t\<rbrace>"
  proof (rule runs_to_weaken[OF bare])
    fix r t
    assume post:
      "due_prefix_generated_terminal_post D now entry all_due future r t"
    show
      "due_prefix_generated_public_post D now entry all_due future t"
      unfolding due_prefix_generated_public_post_def
      by (rule exI[where x = r], rule post)
  qed
  show ?thesis
    by (rule due_prefix_generated_finally_normalises[OF bare_public])
qed

theorem due_prefix_generated_zero_due_finally_loop:
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
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_generated_zero_public_post D now entry future c t\<rbrace>"
proof -
  have bare:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_zero_terminal_post D now entry
       future c\<rbrace>"
    by (rule due_prefix_generated_zero_due_bare_loop[OF empty nonempty])
  have bare_public:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>_ t.
       due_prefix_generated_zero_public_post D now entry future c t\<rbrace>"
  proof (rule runs_to_weaken[OF bare])
    fix r t
    assume post:
      "due_prefix_generated_zero_terminal_post D now entry future c r t"
    show
      "due_prefix_generated_zero_public_post D now entry future c t"
      unfolding due_prefix_generated_zero_public_post_def
      by (rule exI[where x = r], rule post)
  qed
  show ?thesis
    by (rule due_prefix_generated_finally_normalises[OF bare_public])
qed

text \<open>
  Public arbitrary-finite theorem.  Both lists are universally quantified by
  the theorem schema; all task IDs, priorities, ticks, pointers, heap layouts,
  branches and list lengths remain symbolic.  The zero-length due list is an
  explicit case of the same theorem, not a concrete model-checking instance.
\<close>

theorem due_prefix_generated_finally_loop_complete:
  assumes start:
    "due_prefix_generated_start_inv D R now entry due_tasks future
       pxTCB c"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_generated_complete_public_post D now entry
         due_tasks future c t\<rbrace>"
proof -
  have bare:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_complete_terminal_post D now entry
       due_tasks future c\<rbrace>"
    by (rule due_prefix_generated_bare_loop_complete[OF start roots])
  have bare_public:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>_ t.
       due_prefix_generated_complete_public_post D now entry
         due_tasks future c t\<rbrace>"
  proof (rule runs_to_weaken[OF bare])
    fix r t
    assume post:
      "due_prefix_generated_complete_terminal_post D now entry
        due_tasks future c r t"
    show
      "due_prefix_generated_complete_public_post D now entry
        due_tasks future c t"
      unfolding due_prefix_generated_complete_public_post_def
      by (rule exI[where x = r], rule post)
  qed
  show ?thesis
    by (rule due_prefix_generated_finally_normalises[OF bare_public])
qed

end
