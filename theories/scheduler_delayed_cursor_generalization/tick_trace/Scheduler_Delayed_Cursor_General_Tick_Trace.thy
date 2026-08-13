theory Scheduler_Delayed_Cursor_General_Tick_Trace
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure.Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure"
begin

section \<open>Finite generated tick-call sequence\<close>

fun cursor_general_vTaskIncrementTick_calls ::
  "nat \<Rightarrow> (unit, Scheduler_V611_Parse.globals) res_monad"
where
  "cursor_general_vTaskIncrementTick_calls 0 = skip"
| "cursor_general_vTaskIncrementTick_calls (Suc n) =
     bind Scheduler_V611_Delay_Translation.vTaskIncrementTick'
       (\<lambda>_. cursor_general_vTaskIncrementTick_calls n)"

fun task_increment_tick_modular_steps_abs ::
  "nat \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "task_increment_tick_modular_steps_abs 0 a = a"
| "task_increment_tick_modular_steps_abs (Suc n) a =
     task_increment_tick_modular_steps_abs n
       (task_increment_tick_modular_abs a)"

text \<open>
  Rel is a caller-supplied stable boundary invariant.  Its arithmetic premise
  is necessary: the emitted signed overflow increment has no successful run at
  INT_MAX.  The preservation premise mentions only the checked public post,
  not source success or a chosen concrete successor.
\<close>

theorem cursor_general_vTaskIncrementTick_finite_trace:
  fixes Rel ::
    "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
  assumes entry:
    "\<And>c a. Rel c a \<Longrightarrow>
       CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
         termination external"
    and arithmetic:
    "\<And>c a. Rel c a \<Longrightarrow> sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
    and preserved:
    "\<And>c a r t. Rel c a \<Longrightarrow>
       CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
         termination external r t \<Longrightarrow>
       Rel t (task_increment_tick_modular_abs a)"
    and rel: "Rel c a"
  shows
    "cursor_general_vTaskIncrementTick_calls n \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>a'.
       r = Result () \<and>
       Rel t a' \<and>
       a' = task_increment_tick_modular_steps_abs n a\<rbrace>"
  using rel
proof (induction n arbitrary: c a)
  case 0
  show ?case
    apply (simp only: cursor_general_vTaskIncrementTick_calls.simps)
    apply runs_to_vcg
    using "0.prems" by simp
next
  case (Suc n)
  have one:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
       termination external\<rbrace>"
    by (rule
      CursorGeneralStrongVTaskIncrementTickPublicEntryRel_sequential_branch_complete[
        OF entry[OF Suc.prems] arithmetic[OF Suc.prems]])
  show ?case
    apply (simp only: cursor_general_vTaskIncrementTick_calls.simps)
    apply (rule runs_to_bind_res)
    apply (rule runs_to_weaken[OF one])
     apply (frule
       CursorGeneralStrongVTaskIncrementTickPublicCompletePost_result_reentryD)
     apply clarsimp
    apply (rule runs_to_weaken[OF Suc.IH])
     apply (rule preserved)
      apply (rule Suc.prems)
     apply assumption
    by auto
qed

text \<open>
  The theorem is uniform in n and in every scheduler state admitted by Rel.
  It establishes a finite trace for the tick root only; a five-root call
  alphabet and common invariant remain separate obligations.
\<close>

end
