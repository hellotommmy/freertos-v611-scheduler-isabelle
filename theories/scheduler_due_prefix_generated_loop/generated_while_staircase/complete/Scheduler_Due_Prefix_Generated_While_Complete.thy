theory Scheduler_Due_Prefix_Generated_While_Complete
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Zero.Scheduler_Due_Prefix_Generated_While_Zero"
begin

text \<open>
  Unified symbolic entry and terminal post for every finite due-task list,
  including zero length.  The zero branch still quantifies over an arbitrary
  future list and the nonzero branch delegates to the Gate-H indexed theorem.
\<close>

definition due_prefix_generated_start_inv ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_start_inv D R now entry due_tasks future
       pxTCB c \<longleftrightarrow>
     (case due_tasks of
        [] \<Rightarrow>
          (case future of
             [] \<Rightarrow>
               pxTCB = NULL \<and>
               due_prefix_exit_inv now entry [] [] [] entry
                 EmptyExit None
           | f # fs \<Rightarrow>
               (\<exists>k. pxTCB = sd_tcb_ptr D f \<and>
                 due_prefix_exit_inv now entry [] []
                   (Generic f # map Generic fs) entry
                   FutureExit (Some (Generic f)) \<and>
                 due_prefix_future_source_ready D c now entry f k))
      | task # due_tail \<Rightarrow>
          due_prefix_generated_index_inv D R now entry
            (map Generic due_tasks) future due_tail pxTCB c)"

definition due_prefix_generated_complete_terminal_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_complete_terminal_post D now entry due_tasks
       future before r t \<longleftrightarrow>
     (case due_tasks of
        [] \<Rightarrow>
          due_prefix_generated_zero_terminal_post D now entry
            future before r t
      | task # due_tail \<Rightarrow>
          due_prefix_generated_terminal_post D now entry
            (map Generic due_tasks) future r t)"

theorem due_prefix_generated_bare_loop_complete:
  assumes start:
    "due_prefix_generated_start_inv D R now entry due_tasks future
       pxTCB c"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_complete_terminal_post D now entry
       due_tasks future c\<rbrace>"
proof (cases due_tasks)
  case Nil
  have empty:
    "future = [] \<Longrightarrow>
       pxTCB = NULL \<and>
       due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
    using start Nil
    by (cases future)
       (simp_all add: due_prefix_generated_start_inv_def)
  have nonempty:
    "\<And>f fs. future = f # fs \<Longrightarrow>
      \<exists>k. pxTCB = sd_tcb_ptr D f \<and>
        due_prefix_exit_inv now entry [] []
          (Generic f # map Generic fs) entry
          FutureExit (Some (Generic f)) \<and>
        due_prefix_future_source_ready D c now entry f k"
    using start Nil
    by (simp add: due_prefix_generated_start_inv_def)
  have terminal:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_zero_terminal_post D now entry
       future c\<rbrace>"
    by (rule due_prefix_generated_zero_due_bare_loop[OF empty nonempty])
  show ?thesis
  proof (rule runs_to_weaken[OF terminal])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "due_prefix_generated_zero_terminal_post D now entry
         future c r t"
    show
      "due_prefix_generated_complete_terminal_post D now entry
         due_tasks future c r t"
      using post Nil
      by (simp add: due_prefix_generated_complete_terminal_post_def)
  qed
next
  case (Cons task due_tail)
  have index:
    "due_prefix_generated_index_inv D R now entry
       (map Generic due_tasks) future due_tail pxTCB c"
    using start Cons
    by (simp add: due_prefix_generated_start_inv_def)
  have terminal:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_generated_terminal_post D now entry
       (map Generic due_tasks) future\<rbrace>"
    by (rule due_prefix_generated_bare_loop_all_due[OF index roots])
  show ?thesis
  proof (rule runs_to_weaken[OF terminal])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "due_prefix_generated_terminal_post D now entry
         (map Generic due_tasks) future r t"
    show
      "due_prefix_generated_complete_terminal_post D now entry
         due_tasks future c r t"
      using post Cons
      by (simp add: due_prefix_generated_complete_terminal_post_def)
  qed
qed

end
