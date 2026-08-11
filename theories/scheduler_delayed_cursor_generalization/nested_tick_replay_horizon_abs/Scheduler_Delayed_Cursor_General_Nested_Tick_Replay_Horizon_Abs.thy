theory Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Horizon_Abs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Body_Capstone.Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Body_Capstone"
begin

text \<open>
  Pure abstract replay arithmetic.  The predicate below is the literal
  generated unlocked-tick guard after replacing the represented concrete tick
  and overflow words by their abstract scalar observations.  It deliberately
  keeps the no-wrap and wrap-defined branches joined.
\<close>

definition resume_tick_arithmetic_defined_abs ::
  "'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_tick_arithmetic_defined_abs a \<longleftrightarrow>
     (sa_tick a + 1 \<noteq> 0 \<or>
      (0 \<le> 2147483649 +
         sint (of_nat (sa_overflows a) :: 32 signed word) \<and>
       sint (of_nat (sa_overflows a) :: 32 signed word) < INT_MAX))"

fun resume_missed_replay_horizon_safe ::
  "nat \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_missed_replay_horizon_safe 0 a = True"
| "resume_missed_replay_horizon_safe (Suc n) a =
     (resume_tick_arithmetic_defined_abs a \<and>
      resume_missed_replay_horizon_safe n
        (resume_missed_source_step_abs a))"

lemma resume_missed_source_steps_abs_add:
  "resume_missed_source_steps_abs (m + n) a =
     resume_missed_source_steps_abs n
       (resume_missed_source_steps_abs m a)"
  by (induction m arbitrary: a) simp_all

lemma resume_missed_source_steps_abs_missed_ticks:
  "sa_missed_ticks (resume_missed_source_steps_abs n a) =
     sa_missed_ticks a - n"
proof (induction n arbitrary: a)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
    using Suc.IH[of "resume_missed_source_step_abs a"]
    by (simp add: resume_missed_source_step_abs_missed_ticks)
qed

lemma resume_missed_replay_horizon_safe_iff:
  "resume_missed_replay_horizon_safe n a \<longleftrightarrow>
     (\<forall>i<n. resume_tick_arithmetic_defined_abs
       (resume_missed_source_steps_abs i a))"
proof (induction n arbitrary: a)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof
    assume safe: "resume_missed_replay_horizon_safe (Suc n) a"
    have head: "resume_tick_arithmetic_defined_abs a"
      and tail:
        "resume_missed_replay_horizon_safe n
          (resume_missed_source_step_abs a)"
      using safe by simp_all
    have tail_all:
      "\<forall>i<n. resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs i
          (resume_missed_source_step_abs a))"
      using tail Suc.IH by blast
    show
      "\<forall>i<Suc n. resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs i a)"
    proof (intro allI impI)
      fix i
      assume bound: "i < Suc n"
      show
        "resume_tick_arithmetic_defined_abs
          (resume_missed_source_steps_abs i a)"
      proof (cases i)
        case 0
        show ?thesis using head 0 by simp
      next
        case (Suc j)
        have "j < n" using bound Suc by simp
        then have
          "resume_tick_arithmetic_defined_abs
            (resume_missed_source_steps_abs j
              (resume_missed_source_step_abs a))"
          using tail_all by blast
        then show ?thesis using Suc by simp
      qed
    qed
  next
    assume all:
      "\<forall>i<Suc n. resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs i a)"
    have head: "resume_tick_arithmetic_defined_abs a"
      using all[rule_format, of 0] by simp
    have tail_all:
      "\<forall>i<n. resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs i
          (resume_missed_source_step_abs a))"
    proof (intro allI impI)
      fix i
      assume bound: "i < n"
      have successor: "Suc i < Suc n" using bound by simp
      have
        "resume_tick_arithmetic_defined_abs
          (resume_missed_source_steps_abs (Suc i) a)"
        using all successor by blast
      then show
        "resume_tick_arithmetic_defined_abs
          (resume_missed_source_steps_abs i
            (resume_missed_source_step_abs a))"
        by simp
    qed
    have tail:
      "resume_missed_replay_horizon_safe n
        (resume_missed_source_step_abs a)"
      using tail_all Suc.IH by blast
    show "resume_missed_replay_horizon_safe (Suc n) a"
      using head tail by simp
  qed
qed

lemma resume_missed_replay_horizon_safe_positive_shift:
  assumes positive: "0 < sa_missed_ticks a"
    and horizon:
      "resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "resume_tick_arithmetic_defined_abs a \<and>
     resume_missed_replay_horizon_safe
       (sa_missed_ticks (resume_missed_source_step_abs a))
       (resume_missed_source_step_abs a)"
proof -
  obtain n where debt: "sa_missed_ticks a = Suc n"
    using positive by (cases "sa_missed_ticks a") auto
  have head: "resume_tick_arithmetic_defined_abs a"
    and tail:
      "resume_missed_replay_horizon_safe n
        (resume_missed_source_step_abs a)"
    using horizon debt by simp_all
  have remaining:
    "sa_missed_ticks (resume_missed_source_step_abs a) = n"
    using debt by (simp add: resume_missed_source_step_abs_missed_ticks)
  show ?thesis using head tail remaining by simp
qed

ML \<open>
  fun audit_closed label th =
    if null (Thm.hyps_of th) andalso null (Thm.prems_of th) then ()
    else error (label ^ " expected zero hidden hypotheses and zero premises")

  fun audit_0_2 label th =
    if null (Thm.hyps_of th) andalso length (Thm.prems_of th) = 2 then ()
    else error (label ^ " expected zero hidden hypotheses and two premises")

  val _ = audit_closed "missed steps add"
    @{thm resume_missed_source_steps_abs_add}
  val _ = audit_closed "missed steps debt"
    @{thm resume_missed_source_steps_abs_missed_ticks}
  val _ = audit_closed "replay horizon forall equivalence"
    @{thm resume_missed_replay_horizon_safe_iff}
  val _ = audit_0_2 "positive-debt horizon shift"
    @{thm resume_missed_replay_horizon_safe_positive_shift}
\<close>

end
