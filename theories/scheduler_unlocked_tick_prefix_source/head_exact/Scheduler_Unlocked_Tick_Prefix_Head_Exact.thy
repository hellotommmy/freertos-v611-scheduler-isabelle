theory Scheduler_Unlocked_Tick_Prefix_Head_Exact
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Role_Exact.Scheduler_Unlocked_Tick_Prefix_Role_Exact"
begin

text \<open>
  Exact generated delayed-list read after the role factor.  Empty and
  nonempty are source branches, not fixed test instances.  In the nonempty
  branch the result is the actual owner read from the arbitrary heap head;
  no expected TCB pointer appears among the premises.
\<close>

lemma generated_current_delayed_readable_rootD:
  assumes readable: "generated_current_delayed_readable c"
  shows "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
  using readable
  by (simp add: generated_current_delayed_readable_def)

lemma generated_current_delayed_readable_headD:
  assumes readable: "generated_current_delayed_readable c"
    and nonempty: "generated_current_delayed_count c \<noteq> 0"
  shows "c_guard (generated_current_delayed_head c)"
  using readable nonempty
  by (simp add: generated_current_delayed_readable_def)

theorem generated_current_delayed_read_empty_exact:
  assumes root:
    "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    and empty: "generated_current_delayed_count c = 0"
  shows
    "one_due_tick_delayed_remainder \<bullet> c
     \<lbrace>\<lambda>r t. r = Result NULL \<and> t = c\<rbrace>"
  unfolding one_due_tick_delayed_remainder_def
  apply runs_to_vcg
  using root empty
  by (simp_all add: generated_current_delayed_count_def)

theorem generated_current_delayed_read_nonempty_exact:
  assumes root:
    "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    and nonempty: "generated_current_delayed_count c \<noteq> 0"
    and head: "c_guard (generated_current_delayed_head c)"
  shows
    "one_due_tick_delayed_remainder \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result
         (PTR_COERCE(unit \<rightarrow>
            Scheduler_V611_Parse.tskTaskControlBlock_C)
            (generated_current_delayed_owner c)) \<and>
       t = c
     \<rbrace>"
proof -
  have sentinel:
    "c_guard (PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
       &(Scheduler_V611_Parse.globals.pxDelayedTaskList_' c
         \<rightarrow>[''xListEnd_C'']))"
    by (rule one_due_sentinel_mini_guard[OF root])
  show ?thesis
    unfolding one_due_tick_delayed_remainder_def
    apply runs_to_vcg
    using root nonempty head sentinel
    by (simp_all add: generated_current_delayed_count_def
        generated_current_delayed_head_def
        generated_current_delayed_owner_def scheduler_list_head_item_def)
qed

theorem generated_current_delayed_read_exact:
  assumes readable: "generated_current_delayed_readable c"
  shows
    "one_due_tick_delayed_remainder \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (generated_current_delayed_result c) \<and>
       t = c
     \<rbrace>"
proof (cases "generated_current_delayed_count c = 0")
  case True
  have root:
    "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    by (rule generated_current_delayed_readable_rootD[OF readable])
  note empty = generated_current_delayed_read_empty_exact[OF root True]
  show ?thesis
    apply (rule runs_to_weaken[OF empty])
    using True
    by (simp add: generated_current_delayed_result_def)
next
  case False
  have root:
    "c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    by (rule generated_current_delayed_readable_rootD[OF readable])
  have head: "c_guard (generated_current_delayed_head c)"
    by (rule generated_current_delayed_readable_headD[OF readable False])
  note nonempty = generated_current_delayed_read_nonempty_exact[
    OF root False head]
  show ?thesis
    apply (rule runs_to_weaken[OF nonempty])
    using False
    by (simp add: generated_current_delayed_result_def)
qed

end
