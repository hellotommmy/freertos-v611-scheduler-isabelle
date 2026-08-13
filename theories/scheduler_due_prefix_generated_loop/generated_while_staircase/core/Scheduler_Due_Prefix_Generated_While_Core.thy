theory Scheduler_Due_Prefix_Generated_While_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Source.Scheduler_Due_Prefix_Terminal_Source"
begin

text \<open>
  Cacheable core rung for the generated-while staircase.

  Exception-aware finite-list induction for an actual @{const whileLoop}.
  The empty index is deliberately allowed to have its guard true: this is the
  generated FreeRTOS future-head case, whose body throws before mutating the
  scheduler state.  A nonempty index consumes exactly one arbitrary element
  on each normal body result.  Exceptional outcomes are terminal and are never
  fed back into the loop.

  This rule is intentionally separate from @{thm runs_to_whileLoop_variant_res}.
  The latter is a result-only rule and cannot justify a loop whose specified
  terminal path is an exception.
\<close>

theorem runs_to_whileLoop_exn_list_induct:
  fixes C :: "'a \<Rightarrow> 's \<Rightarrow> bool"
    and B :: "'a \<Rightarrow> ('e, 'a, 's) exn_monad"
    and I :: "'i list \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
    and P :: "('e, 'a) xval \<Rightarrow> 's \<Rightarrow> bool"
  assumes nil_result:
      "\<And>a s. I [] a s \<Longrightarrow> \<not> C a s \<Longrightarrow>
        P (Result a) s"
    and nil_body:
      "\<And>a s. I [] a s \<Longrightarrow> C a s \<Longrightarrow>
        B a \<bullet> s
        \<lbrace>\<lambda>r t.
          (\<forall>b. r = Result b \<longrightarrow> False) \<and>
          (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)\<rbrace>"
    and cons_guard:
      "\<And>x xs a s. I (x # xs) a s \<Longrightarrow> C a s"
    and cons_body:
      "\<And>x xs a s. I (x # xs) a s \<Longrightarrow>
        B a \<bullet> s
        \<lbrace>\<lambda>r t.
          (\<forall>b. r = Result b \<longrightarrow> I xs b t) \<and>
          (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)\<rbrace>"
    and init: "I xs a s"
  shows "whileLoop C B a \<bullet> s \<lbrace>P\<rbrace>"
  using init
proof (induction xs arbitrary: a s)
  case Nil
  show ?case
  proof (rule runs_to_whileLoop_unroll_exn)
    show "\<not> C a s \<Longrightarrow> P (Result a) s"
      by (rule nil_result[OF Nil.prems])
    show "C a s \<Longrightarrow>
      B a \<bullet> s
      \<lbrace>\<lambda>r t.
        (\<forall>b. r = Result b \<longrightarrow>
          whileLoop C B b \<bullet> t \<lbrace>P\<rbrace>) \<and>
        (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)\<rbrace>"
    proof -
      assume guard: "C a s"
      show ?thesis
      proof (rule runs_to_weaken[OF nil_body[OF Nil.prems guard]])
        fix r :: "('e, 'a) xval"
        fix t :: 's
        assume terminal:
          "(\<forall>b. r = Result b \<longrightarrow> False) \<and>
           (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)"
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop C B b \<bullet> t \<lbrace>P\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)"
          using terminal by blast
      qed
    qed
  qed
next
  case (Cons x xs)
  have guard: "C a s"
    by (rule cons_guard[OF Cons.prems])
  show ?case
  proof (rule runs_to_whileLoop_unroll_exn)
    show "\<not> C a s \<Longrightarrow> P (Result a) s"
      using guard by blast
    show "C a s \<Longrightarrow>
      B a \<bullet> s
      \<lbrace>\<lambda>r t.
        (\<forall>b. r = Result b \<longrightarrow>
          whileLoop C B b \<bullet> t \<lbrace>P\<rbrace>) \<and>
        (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)\<rbrace>"
    proof -
      assume "C a s"
      show ?thesis
      proof (rule runs_to_weaken[OF cons_body[OF Cons.prems]])
        fix r :: "('e, 'a) xval"
        fix t :: 's
        assume step:
          "(\<forall>b. r = Result b \<longrightarrow> I xs b t) \<and>
           (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)"
        have recurse:
          "\<forall>b. r = Result b \<longrightarrow>
             whileLoop C B b \<bullet> t \<lbrace>P\<rbrace>"
        proof (intro allI impI)
          fix b
          assume result: "r = Result b"
          have "I xs b t"
            using step result by blast
          then show "whileLoop C B b \<bullet> t \<lbrace>P\<rbrace>"
            by (rule Cons.IH)
        qed
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop C B b \<bullet> t \<lbrace>P\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t)"
          using recurse step by blast
      qed
    qed
  qed
qed

text \<open>
  The exact generated subterm below is the delayed-task while and its CParser
  exception normalisation, factored out of @{const one_due_tick_unlocked_source}.
  The loop guard is pointer non-nullity.  In particular, a non-null future head
  enters the body and throws; only the empty residual ring takes the false
  guard.
\<close>

definition due_prefix_generated_bare_loop ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr,
     Scheduler_V611_Parse.globals) exn_monad"
where
  "due_prefix_generated_bare_loop pxTCB =
     whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
       one_due_tick_loop_body_source pxTCB"

definition due_prefix_generated_finally_loop ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   (unit, unit, Scheduler_V611_Parse.globals) spec_monad"
where
  "due_prefix_generated_finally_loop pxTCB =
     finally (do {
       pxTCB \<leftarrow> due_prefix_generated_bare_loop pxTCB;
       skip
     })"

lemma due_prefix_generated_bare_loop_unfold:
  "due_prefix_generated_bare_loop pxTCB =
     whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
       one_due_tick_loop_body_source pxTCB"
  by (simp add: due_prefix_generated_bare_loop_def)

end
