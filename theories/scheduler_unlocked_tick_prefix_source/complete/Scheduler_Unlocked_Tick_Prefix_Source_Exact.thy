theory Scheduler_Unlocked_Tick_Prefix_Source_Exact
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Head_Exact.Scheduler_Unlocked_Tick_Prefix_Head_Exact"
begin

text \<open>
  Composition of the exact arithmetic/role factor with the exact
  count/head/owner factor.  The post-state is the canonical concrete
  tick-role entry state and the return is determined solely by its physical
  delayed-list contents.
\<close>

theorem generated_unlocked_tick_prefix_source_defined_exact:
  assumes defined: "generated_unlocked_tick_arithmetic_defined c"
    and readable:
      "generated_current_delayed_readable
         (scheduler_tick_role_entry_state c)"
  shows
    "generated_unlocked_tick_prefix_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c)) \<and>
       t = scheduler_tick_role_entry_state c
     \<rbrace>"
proof -
  note role = generated_unlocked_tick_role_source_defined_exact[OF defined]
  note head = generated_current_delayed_read_exact[OF readable]
  show ?thesis
    unfolding generated_unlocked_tick_prefix_source_split
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF role])
     apply clarsimp
    apply (rule head)
    done
qed

corollary generated_unlocked_tick_prefix_source_defined_empty_exact:
  assumes defined: "generated_unlocked_tick_arithmetic_defined c"
    and readable:
      "generated_current_delayed_readable
         (scheduler_tick_role_entry_state c)"
    and empty:
      "generated_current_delayed_count
         (scheduler_tick_role_entry_state c) = 0"
  shows
    "generated_unlocked_tick_prefix_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result NULL \<and>
       t = scheduler_tick_role_entry_state c
     \<rbrace>"
  apply (rule runs_to_weaken[
    OF generated_unlocked_tick_prefix_source_defined_exact[
      OF defined readable]])
  using empty
  by (simp add: generated_current_delayed_result_def)

corollary generated_unlocked_tick_prefix_source_defined_nonempty_exact:
  assumes defined: "generated_unlocked_tick_arithmetic_defined c"
    and readable:
      "generated_current_delayed_readable
         (scheduler_tick_role_entry_state c)"
    and nonempty:
      "generated_current_delayed_count
         (scheduler_tick_role_entry_state c) \<noteq> 0"
  shows
    "generated_unlocked_tick_prefix_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result
         (PTR_COERCE(unit \<rightarrow>
            Scheduler_V611_Parse.tskTaskControlBlock_C)
            (generated_current_delayed_owner
              (scheduler_tick_role_entry_state c))) \<and>
       t = scheduler_tick_role_entry_state c
     \<rbrace>"
  apply (rule runs_to_weaken[
    OF generated_unlocked_tick_prefix_source_defined_exact[
      OF defined readable]])
  using nonempty
  by (simp add: generated_current_delayed_result_def)

lemma generated_unlocked_tick_prefix_source_undefined_has_no_run:
  assumes undefined: "\<not> generated_unlocked_tick_arithmetic_defined c"
  shows "\<not> succeeds generated_unlocked_tick_prefix_source c"
proof -
  have role:
    "\<not> succeeds generated_unlocked_tick_role_source c"
    by (rule generated_unlocked_tick_role_source_undefined_has_no_run[
          OF undefined])
  show ?thesis
    unfolding generated_unlocked_tick_prefix_source_split
    using role by (auto simp: succeeds_bind)
qed

theorem generated_unlocked_tick_prefix_source_success_implies_defined:
  assumes run: "succeeds generated_unlocked_tick_prefix_source c"
  shows "generated_unlocked_tick_arithmetic_defined c"
proof (rule ccontr)
  assume undefined: "\<not> generated_unlocked_tick_arithmetic_defined c"
  have "\<not> succeeds generated_unlocked_tick_prefix_source c"
    by (rule generated_unlocked_tick_prefix_source_undefined_has_no_run[
          OF undefined])
  then show False using run by contradiction
qed

theorem generated_unlocked_tick_prefix_source_all_arithmetic_inputs:
  assumes readable:
    "generated_current_delayed_readable
       (scheduler_tick_role_entry_state c)"
  shows
    "(if generated_unlocked_tick_arithmetic_defined c
      then generated_unlocked_tick_prefix_source \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result
            (generated_current_delayed_result
              (scheduler_tick_role_entry_state c)) \<and>
          t = scheduler_tick_role_entry_state c
        \<rbrace>
      else \<not> succeeds generated_unlocked_tick_prefix_source c)"
proof (cases "generated_unlocked_tick_arithmetic_defined c")
  case True
  then show ?thesis
    using generated_unlocked_tick_prefix_source_defined_exact[
      OF True readable] by simp
next
  case False
  then show ?thesis
    using generated_unlocked_tick_prefix_source_undefined_has_no_run[
      OF False] by simp
qed

end
