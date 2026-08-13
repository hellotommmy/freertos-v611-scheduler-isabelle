theory Scheduler_Tick_Entry_Pending_Boundary
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_General_Relation.Scheduler_Resume_General_Relation"
begin

text \<open>
  A zero suspend depth is not, by itself, a stable scheduler boundary:
  xTaskResumeAll transiently decrements the depth before draining the pending
  ready list.  The implication below therefore records the missing entry
  condition without excluding suspended intermediate states.  It is a
  boundary invariant, not an extra restriction on task identities, list
  lengths, priorities, ticks, keys, or cursors.
\<close>

definition tick_entry_pending_wf :: "'tid scheduler_abs \<Rightarrow> bool"
where
  "tick_entry_pending_wf s \<longleftrightarrow>
     (sa_suspend_depth s = 0 \<longrightarrow> ring (sa_pending s) = [])"

lemma tick_entry_pending_wfI:
  assumes quiet:
    "sa_suspend_depth s = 0 \<Longrightarrow> ring (sa_pending s) = []"
  shows "tick_entry_pending_wf s"
  using quiet by (simp add: tick_entry_pending_wf_def)

lemma tick_entry_pending_wfD:
  assumes entry: "tick_entry_pending_wf s"
    and unlocked: "sa_suspend_depth s = 0"
  shows "ring (sa_pending s) = []"
  using entry unlocked by (simp add: tick_entry_pending_wf_def)

lemma settled_wf_establishes_tick_entry_pending_wf:
  assumes "settled_wf s"
  shows "tick_entry_pending_wf s"
  using assms
  by (simp add: settled_wf_def tick_entry_pending_wf_def)

lemma yield_pending_wf_establishes_tick_entry_pending_wf:
  assumes "yield_pending_wf s"
  shows "tick_entry_pending_wf s"
  using assms
  by (simp add: yield_pending_wf_def tick_entry_pending_wf_def)

lemma suspended_establishes_tick_entry_pending_wf:
  assumes "sa_suspend_depth s \<noteq> 0"
  shows "tick_entry_pending_wf s"
  using assms by (simp add: tick_entry_pending_wf_def)

lemma tick_entry_pending_wf_drain_pending_abs_empty:
  assumes entry: "tick_entry_pending_wf s"
    and unlocked: "sa_suspend_depth s = 0"
  shows "drain_pending_abs s = s"
  using tick_entry_pending_wfD[OF entry unlocked]
  by simp

text \<open>
  The drain proof follows the actual pending-ring order.  No existential
  successor is introduced: after consuming the Event at the head, remove1
  leaves exactly the tail that indexes the induction hypothesis.
\<close>

lemma tick_entry_resume_one_pending_abs_pending [simp]:
  "sa_pending (resume_one_pending_abs t s) =
     list_remove_abs (Event t) (sa_pending s)"
  by (simp add: resume_one_pending_abs_def resume_remove_generic_abs_def
      resume_add_ready_with_key_abs_def Let_def)

lemma tick_entry_resume_one_pending_abs_suspend_depth [simp]:
  "sa_suspend_depth (resume_one_pending_abs t s) = sa_suspend_depth s"
  by (simp add: resume_one_pending_abs_def resume_remove_generic_abs_def
      resume_add_ready_with_key_abs_def Let_def)

lemma tick_entry_drain_pending_nodes_abs_consumes_events:
  assumes events:
    "\<forall>n\<in>set ns. \<exists>t. n = Event t"
    and pending: "ring (sa_pending s) = ns"
  shows
    "ring (sa_pending (drain_pending_nodes_abs ns s)) = []"
  using events pending
proof (induction ns arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  obtain t where n_event: "n = Event t"
    using Cons.prems(1) by auto
  have tail_events: "\<forall>m\<in>set ns. \<exists>u. m = Event u"
    using Cons.prems(1) by auto
  have pending_tail:
    "ring (sa_pending (resume_one_pending_abs t s)) = ns"
    using Cons.prems(2) n_event
    by (simp add: list_remove_abs_def)
  have tail_empty:
    "ring (sa_pending
       (drain_pending_nodes_abs ns (resume_one_pending_abs t s))) = []"
    by (rule Cons.IH[OF tail_events pending_tail])
  show ?case
    using tail_empty n_event by simp
qed

lemma event_ring_drain_pending_abs_empty:
  assumes event: "event_ring (sa_pending s)"
  shows "ring (sa_pending (drain_pending_abs s)) = []"
proof -
  have events:
    "\<forall>n\<in>set (ring (sa_pending s)). \<exists>t. n = Event t"
    using event by (simp add: event_ring_def)
  show ?thesis
    unfolding drain_pending_abs_def
    by (rule tick_entry_drain_pending_nodes_abs_consumes_events[OF events refl])
qed

corollary core_wf_drain_pending_abs_empty:
  assumes wf: "core_wf s"
  shows "ring (sa_pending (drain_pending_abs s)) = []"
proof -
  have "event_ring (sa_pending s)"
    using wf by (simp add: core_wf_def role_wf_def)
  then show ?thesis
    by (rule event_ring_drain_pending_abs_empty)
qed

lemma tick_entry_drain_pending_nodes_abs_suspend_depth [simp]:
  "sa_suspend_depth (drain_pending_nodes_abs ns s) = sa_suspend_depth s"
proof (induction ns arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  then show ?case by (cases n) simp_all
qed

lemma tick_entry_drain_pending_abs_suspend_depth [simp]:
  "sa_suspend_depth (drain_pending_abs s) = sa_suspend_depth s"
  by (simp add: drain_pending_abs_def)

corollary core_wf_drain_pending_abs_establishes_tick_entry_pending_wf:
  assumes wf: "core_wf s"
  shows "tick_entry_pending_wf (drain_pending_abs s)"
  using core_wf_drain_pending_abs_empty[OF wf]
  by (simp add: tick_entry_pending_wf_def)

text \<open>Frame facts for unlocked ticks and missed-tick replay.\<close>

lemma tick_entry_add_ready_node_pending [simp]:
  "sa_pending (add_ready_node n s) = sa_pending s"
  by (cases n) (simp_all add: Let_def)

lemma tick_entry_add_ready_node_suspend_depth [simp]:
  "sa_suspend_depth (add_ready_node n s) = sa_suspend_depth s"
  by (cases n) (simp_all add: Let_def)

lemma tick_entry_fold_add_ready_node_pending [simp]:
  "sa_pending (fold add_ready_node ns s) = sa_pending s"
  by (induction ns arbitrary: s) simp_all

lemma tick_entry_fold_add_ready_node_suspend_depth [simp]:
  "sa_suspend_depth (fold add_ready_node ns s) = sa_suspend_depth s"
  by (induction ns arbitrary: s) simp_all

lemma tick_unlocked_abs_pending_frame [simp]:
  "sa_pending (tick_unlocked_abs s) = sa_pending s"
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma tick_unlocked_abs_suspend_depth_frame [simp]:
  "sa_suspend_depth (tick_unlocked_abs s) = sa_suspend_depth s"
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma replay_missed_abs_pending_frame [simp]:
  "sa_pending (replay_missed_abs n s) = sa_pending s"
  by (induction n arbitrary: s) simp_all

lemma replay_missed_abs_suspend_depth_frame [simp]:
  "sa_suspend_depth (replay_missed_abs n s) = sa_suspend_depth s"
  by (induction n arbitrary: s) simp_all

lemma request_yield_pending_frame [simp]:
  "sa_pending (request_yield s) = sa_pending s"
  by (simp add: request_yield_def)

lemma request_yield_suspend_depth_frame [simp]:
  "sa_suspend_depth (request_yield s) = sa_suspend_depth s"
  by (simp add: request_yield_def)

lemma YieldAbs_tick_entry_frames:
  assumes yield: "YieldAbs requested s yielded t"
  shows
    "sa_pending t = sa_pending s \<and>
     sa_suspend_depth t = sa_suspend_depth s"
  using yield
  by (auto simp: YieldAbs_def request_yield_def split: if_splits)

lemma task_increment_tick_abs_pending_frame [simp]:
  "sa_pending (task_increment_tick_abs s) = sa_pending s"
  by (simp add: task_increment_tick_abs_def)

lemma task_increment_tick_abs_suspend_depth_frame [simp]:
  "sa_suspend_depth (task_increment_tick_abs s) = sa_suspend_depth s"
  by (simp add: task_increment_tick_abs_def)

theorem task_increment_tick_abs_preserves_tick_entry_pending_wf:
  assumes entry: "tick_entry_pending_wf s"
  shows "tick_entry_pending_wf (task_increment_tick_abs s)"
  using entry
  by (simp add: tick_entry_pending_wf_def)

text \<open>
  core_wf already guarantees a nonempty runnable domain through its ready
  cache witness.  This rules out the ResumeRel live-empty early return for a
  legal scheduler state, without adding a separate nonemptiness premise.
\<close>

lemma tick_entry_core_wf_live_nonempty:
  assumes wf: "core_wf s"
  shows "sa_live s \<noteq> {}"
proof -
  obtain p where p_lt: "p < 4"
      and ready_nonempty: "ring (sa_ready s p) \<noteq> []"
    using wf
    by (auto simp: core_wf_def ready_cache_wf_def)
  obtain n ns where ready_ring: "ring (sa_ready s p) = n # ns"
    using ready_nonempty by (cases "ring (sa_ready s p)") auto
  have ready_ring_generic: "generic_ring (sa_ready s p)"
    using wf p_lt
    by (simp add: core_wf_def role_wf_def)
  have ready_generic:
    "\<forall>n\<in>set (ring (sa_ready s p)). \<exists>t. n = Generic t"
    using ready_ring_generic
    by (simp add: generic_ring_def)
  have n_member: "n \<in> set (ring (sa_ready s p))"
    using ready_ring by simp
  obtain t where n_generic: "n = Generic t"
    using ready_generic n_member by blast
  have t_ready: "t \<in> ready_task_set s"
    unfolding ready_task_set_def
  proof (rule UN_I[where a = p])
    show "p \<in> {0..<4}"
      using p_lt by simp
    show "t \<in> generic_task_set (sa_ready s p)"
      using ready_ring n_generic
      by (simp add: generic_task_set_def)
  qed
  have membership:
    "ready_task_set s \<union>
       generic_task_set (sa_delayed_a s) \<union>
       generic_task_set (sa_delayed_b s) \<union>
       generic_task_set (sa_suspended s) = sa_live s"
    using wf
    by (simp add: core_wf_def membership_wf_def Let_def)
  show ?thesis
    using membership t_ready by blast
qed

theorem ResumeRel_establishes_tick_entry_pending_wf:
  assumes wf: "core_wf s"
    and resume: "ResumeRel s yielded t"
  shows "tick_entry_pending_wf t"
proof (rule tick_entry_pending_wfI)
  assume t_unlocked: "sa_suspend_depth t = 0"
  let ?s0 =
    "s\<lparr>sa_suspend_depth := sa_suspend_depth s - 1\<rparr>"
  have live: "sa_live s \<noteq> {}"
    by (rule tick_entry_core_wf_live_nonempty[OF wf])
  have live0: "sa_live ?s0 \<noteq> {}"
    using live by simp
  have s0_unlocked: "sa_suspend_depth ?s0 = 0"
  proof (rule ccontr)
    assume not_zero: "sa_suspend_depth ?s0 \<noteq> 0"
    have early: "\<not> yielded \<and> t = ?s0"
      using resume not_zero
      by (simp add: ResumeRel_def Let_def)
    show False
      using early t_unlocked not_zero by simp
  qed
  have event: "event_ring (sa_pending s)"
    using wf by (simp add: core_wf_def role_wf_def)
  have event0: "event_ring (sa_pending ?s0)"
    using event by simp
  let ?requested = "resume_yield_required ?s0"
  let ?s1 = "drain_pending_abs ?s0"
  let ?s2 = "replay_missed_abs (sa_missed_ticks ?s1) ?s1"
  let ?caller =
    "if ?requested
     then ?s2\<lparr>sa_missed_yield := False\<rparr>
     else ?s2"
  have drain_empty: "ring (sa_pending ?s1) = []"
    by (rule event_ring_drain_pending_abs_empty[OF event0])
  have caller_empty: "ring (sa_pending ?caller) = []"
    using drain_empty by simp
  have resume_main:
    "\<not> (sa_suspend_depth ?s0 \<noteq> 0 \<or> sa_live ?s0 = {})"
    using s0_unlocked live0 by blast
  have yield_rel: "YieldAbs ?requested ?caller yielded t"
    using resume resume_main
    by (auto simp only: ResumeRel_def Let_def if_False)
  have pending_frame: "sa_pending t = sa_pending ?caller"
    using YieldAbs_tick_entry_frames[OF yield_rel] by simp
  show "ring (sa_pending t) = []"
    using caller_empty pending_frame by simp
qed

end
