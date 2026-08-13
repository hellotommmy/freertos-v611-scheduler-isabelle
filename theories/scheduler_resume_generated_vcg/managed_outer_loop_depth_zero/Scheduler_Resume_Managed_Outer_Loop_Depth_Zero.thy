theory Scheduler_Resume_Managed_Outer_Loop_Depth_Zero
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Nested.Scheduler_Resume_Managed_Outer_Loop_Nested"
begin

text \<open>
  A zero suspension word follows the same concrete early-return branch as a
  legal nested resume: unsigned subtraction wraps it to MAX_WORD, which is
  nonzero.  It is nevertheless outside the abstract Resume API domain.
  These theorems record both facts without weakening the nested refinement or
  pretending that nat subtraction represents the machine underflow.
\<close>

theorem scheduler_xTaskResumeAll_zero_underflow_exact:
  assumes zero:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and>
       t = resume_outer_generated_public_state c \<and>
       Scheduler_V611_Parse.globals.uxSchedulerSuspended_' t =
         (- 1 :: 32 word)\<rbrace>"
proof -
  have branch:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c - 1 \<noteq> 0"
    using zero by simp
  note source = scheduler_xTaskResumeAll_inner_exact[
      OF branch depth interrupts]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using zero
    by (simp add: scheduler_resume_inner_state_def
        resume_outer_generated_public_state_def)
qed

lemma ResumeRel_zero_depth_invalid:
  assumes zero: "sa_suspend_depth a = 0"
  shows "\<not> ResumeRel a yielded b"
  using zero by (simp add: ResumeRel_def)

lemma CursorGeneralStrongSchedulerModularEndpointRel_zero_underflow_impossible:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and zero: "sa_suspend_depth a = 0"
  shows
    "\<not> CursorGeneralStrongSchedulerModularEndpointRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed termination external"
proof -
  have before_count:
    "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a"
    by (rule CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD[
        OF endpoint])
  have concrete_zero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    using before_count zero by (simp add: unat_eq_zero)
  show ?thesis
  proof
    assume after:
      "CursorGeneralStrongSchedulerModularEndpointRel
         D (resume_outer_generated_public_state c)
         (resume_outer_entry_abs a) managed termination external"
    have after_count:
      "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
        (resume_outer_generated_public_state c)) =
       sa_suspend_depth (resume_outer_entry_abs a)"
      by (rule CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD[
          OF after])
    have abstract_zero:
      "sa_suspend_depth (resume_outer_entry_abs a) = 0"
      using zero by (simp add: resume_outer_entry_abs_def)
    have concrete_max:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
        (resume_outer_generated_public_state c) = (- 1 :: 32 word)"
      using concrete_zero
      by (simp add: resume_outer_generated_public_state_def)
    have max_zero: "(- 1 :: 32 word) = 0"
      using after_count abstract_zero concrete_max
      by (simp add: unat_eq_zero)
    show False
      using max_zero by simp
  qed
qed

theorem
  CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_depth_zero_invalid:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and zero: "sa_suspend_depth a = 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and>
       t = resume_outer_generated_public_state c \<and>
       Scheduler_V611_Parse.globals.uxSchedulerSuspended_' t =
         (- 1 :: 32 word) \<and>
       \<not> ResumeRel a False (resume_outer_entry_abs a) \<and>
       \<not> CursorGeneralStrongSchedulerModularEndpointRel
         D t (resume_outer_entry_abs a)
         managed termination external\<rbrace>"
proof -
  have count:
    "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a"
    by (rule CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD[
        OF endpoint])
  have concrete_zero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    using count zero by (simp add: unat_eq_zero)
  have boundary: "scheduler_boundary_rel c"
    by (rule CursorGeneralStrongSchedulerModularEndpointRel_boundaryD[
        OF endpoint])
  have depth:
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    using boundary by (simp_all add: scheduler_boundary_rel_def)
  note source = scheduler_xTaskResumeAll_zero_underflow_exact[
      OF concrete_zero depth interrupts]
  have invalid:
    "\<not> ResumeRel a False (resume_outer_entry_abs a)"
    by (rule ResumeRel_zero_depth_invalid[OF zero])
  have no_endpoint:
    "\<not> CursorGeneralStrongSchedulerModularEndpointRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed termination external"
    by (rule
      CursorGeneralStrongSchedulerModularEndpointRel_zero_underflow_impossible[
        OF endpoint zero])
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using invalid no_endpoint by blast
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "zero-depth exact machine underflow" 3
    @{thm scheduler_xTaskResumeAll_zero_underflow_exact}
  val _ = audit_exact "zero-depth Resume domain exclusion" 1
    @{thm ResumeRel_zero_depth_invalid}
  val _ = audit_exact "zero-depth endpoint incompatibility" 2
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_zero_underflow_impossible}
  val _ = audit_exact "actual generated zero-depth classification" 2
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_depth_zero_invalid}
\<close>

end
