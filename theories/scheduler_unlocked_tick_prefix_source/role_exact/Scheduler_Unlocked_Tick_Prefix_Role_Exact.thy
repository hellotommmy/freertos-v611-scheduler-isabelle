theory Scheduler_Unlocked_Tick_Prefix_Role_Exact
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Factors.Scheduler_Unlocked_Tick_Prefix_Source_Factors"
begin

text \<open>
  The arithmetic split is exhaustive over all 32-bit tick and overflow words.
  Tick wrap is an ordinary modular transition.  Only the generated signed
  overflow increment can be undefined, and then the source factor has no
  successor before it reaches the delayed-list read.
\<close>

lemma generated_unlocked_tick_arithmetic_defined_iff:
  "generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
     tick_unlocked_signed_defined c"
  by (auto simp: generated_unlocked_tick_arithmetic_defined_def
      tick_unlocked_signed_defined_def tick_overflow_increment_defined_def)

lemma generated_unlocked_tick_arithmetic_class_iff:
  "generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
     classify_generated_tick_arithmetic c \<noteq> TickWrapSignedOverflow"
  by (auto simp: generated_unlocked_tick_arithmetic_defined_def
      classify_generated_tick_arithmetic_def
      tick_overflow_increment_defined_def)

lemma generated_unlocked_tick_arithmetic_undefined_iff:
  "\<not> generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
     Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0 \<and>
     \<not> tick_overflow_increment_defined c"
  by (auto simp: generated_unlocked_tick_arithmetic_defined_def
      tick_overflow_increment_defined_def)

theorem generated_unlocked_tick_role_source_no_wrap_exact:
  assumes no_wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 \<noteq> 0"
  shows
    "generated_unlocked_tick_role_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_tick_role_entry_state c
     \<rbrace>"
  unfolding generated_unlocked_tick_role_source_def
  apply runs_to_vcg
  using no_wrap
  by (simp_all add: scheduler_tick_role_entry_state_def Let_def)

theorem generated_unlocked_tick_role_source_wrap_defined_exact:
  assumes wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0"
    and defined: "tick_overflow_increment_defined c"
  shows
    "generated_unlocked_tick_role_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_tick_role_entry_state c
     \<rbrace>"
proof -
  have lower:
    "0 \<le> 2147483649 +
       sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c)"
    and upper:
    "sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) < INT_MAX"
    using defined
    by (simp_all add: tick_overflow_increment_defined_def)
  show ?thesis
    unfolding generated_unlocked_tick_role_source_def
    apply runs_to_vcg
    using wrap lower upper
    by (simp_all add: scheduler_tick_role_entry_state_def Let_def)
qed

theorem generated_unlocked_tick_role_source_defined_exact:
  assumes defined: "generated_unlocked_tick_arithmetic_defined c"
  shows
    "generated_unlocked_tick_role_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_tick_role_entry_state c
     \<rbrace>"
proof (cases
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0")
  case False
  show ?thesis
    by (rule generated_unlocked_tick_role_source_no_wrap_exact[OF False])
next
  case True
  have overflow_defined: "tick_overflow_increment_defined c"
    using defined True
    by (auto simp: generated_unlocked_tick_arithmetic_defined_def
        tick_overflow_increment_defined_def)
  show ?thesis
    by (rule generated_unlocked_tick_role_source_wrap_defined_exact[
          OF True overflow_defined])
qed

lemma generated_unlocked_tick_role_source_undefined_has_no_run:
  assumes undefined: "\<not> generated_unlocked_tick_arithmetic_defined c"
  shows "\<not> succeeds generated_unlocked_tick_role_source c"
proof -
  have wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0"
    and overflow_undefined: "\<not> tick_overflow_increment_defined c"
    using generated_unlocked_tick_arithmetic_undefined_iff[of c]
      undefined by blast+
  show ?thesis
    using wrap overflow_undefined
    unfolding generated_unlocked_tick_role_source_def
    by (auto simp: tick_overflow_increment_defined_def succeeds_bind)
qed

theorem generated_unlocked_tick_role_source_success_iff_defined:
  "succeeds generated_unlocked_tick_role_source c \<longleftrightarrow>
     generated_unlocked_tick_arithmetic_defined c"
proof
  assume succeeds: "succeeds generated_unlocked_tick_role_source c"
  show "generated_unlocked_tick_arithmetic_defined c"
  proof (rule ccontr)
    assume undefined: "\<not> generated_unlocked_tick_arithmetic_defined c"
    then have "\<not> succeeds generated_unlocked_tick_role_source c"
      by (rule generated_unlocked_tick_role_source_undefined_has_no_run)
    then show False using succeeds by contradiction
  qed
next
  assume defined: "generated_unlocked_tick_arithmetic_defined c"
  have run:
    "generated_unlocked_tick_role_source \<bullet> c
     \<lbrace>\<lambda>_ _. True\<rbrace>"
    by (rule runs_to_weaken[
          OF generated_unlocked_tick_role_source_defined_exact[OF defined]])
       simp
  show "succeeds generated_unlocked_tick_role_source c"
    using run by (simp add: succeeds_runs_to_iff)
qed

end
