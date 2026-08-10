theory Scheduler_Unlocked_Tick_Prefix_Source_Factors
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Outer_Tick_Contract.Scheduler_Outer_Tick_Contract"
begin

text \<open>
  Exact source-order factorisation of the generated unlocked tick prefix.
  The first factor performs only the modular tick increment, the conditional
  delayed-root role swap, the two literal signed-overflow guards, and the
  overflow-counter increment.  The second factor is the existing generated
  delayed-list count/head/owner read.  No runtime input is specialised.
\<close>

definition generated_unlocked_tick_role_source ::
  "(unit, unit, Scheduler_V611_Parse.globals) spec_monad"
where
  "generated_unlocked_tick_role_source = do {
     modify
       (Scheduler_V611_Parse.globals.xTickCount_'_update (\<lambda>w. w + 1));
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.xTickCount_' s = 0)
       (do {
         pxTemp \<leftarrow> gets
           Scheduler_V611_Parse.globals.pxDelayedTaskList_';
         modify
           (\<lambda>s. s\<lparr>Scheduler_V611_Parse.globals.pxDelayedTaskList_' :=
             Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s\<rparr>);
         modify
           (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
             (\<lambda>_. pxTemp));
         guard
           (\<lambda>s. 0 \<le> 2147483649 +
             sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' s));
         guard
           (\<lambda>s. sint
             (Scheduler_V611_Parse.globals.xNumOfOverflows_' s) < INT_MAX);
         modify
           (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
             (\<lambda>w. w + 1))
       })
       skip
   }"

definition generated_current_delayed_count ::
  "Scheduler_V611_Parse.globals \<Rightarrow> 32 word"
where
  "generated_current_delayed_count c =
     Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c))"

definition generated_current_delayed_head ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr"
where
  "generated_current_delayed_head c =
     scheduler_list_head_item
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"

definition generated_current_delayed_owner ::
  "Scheduler_V611_Parse.globals \<Rightarrow> unit ptr"
where
  "generated_current_delayed_owner c =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (generated_current_delayed_head c))"

definition generated_current_delayed_result ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
where
  "generated_current_delayed_result c =
     (if generated_current_delayed_count c = 0
      then NULL
      else PTR_COERCE(unit \<rightarrow>
             Scheduler_V611_Parse.tskTaskControlBlock_C)
             (generated_current_delayed_owner c))"

definition generated_current_delayed_readable ::
  "Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "generated_current_delayed_readable c \<longleftrightarrow>
     c_guard (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) \<and>
     (generated_current_delayed_count c \<noteq> 0 \<longrightarrow>
       c_guard (generated_current_delayed_head c))"

lemma generated_unlocked_tick_prefix_source_split:
  "generated_unlocked_tick_prefix_source = do {
     generated_unlocked_tick_role_source;
     one_due_tick_delayed_remainder
   }"
  unfolding generated_unlocked_tick_prefix_source_def
    generated_unlocked_tick_role_source_def
    one_due_tick_delayed_remainder_def
  by (simp add: bind_assoc)

end
