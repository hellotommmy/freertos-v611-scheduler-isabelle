theory Scheduler_Resume_Managed_Modular_Endpoint
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Replay_Split.Scheduler_Resume_Managed_Replay_Split"
begin

definition normalize_yield_count_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "normalize_yield_count_abs a =
     a\<lparr>sa_yield_count :=
       unat (of_nat (sa_yield_count a) :: 32 word)\<rparr>"

definition CursorGeneralStrongSchedulerModularEndpointRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> bool"
where
  "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external \<longleftrightarrow>
     CursorGeneralStrongSchedulerEndpointRel
       D c (normalize_yield_count_abs a)
       managed termination external \<and>
     yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
       (sa_yield_count a)"

definition CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow> bool"
where
  "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external \<longleftrightarrow>
     CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c (normalize_yield_count_abs a)
       managed termination external \<and>
     yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
       (sa_yield_count a)"

lemma normalize_yield_count_abs_components:
  "sa_live (normalize_yield_count_abs a) = sa_live a \<and>
   sa_priority (normalize_yield_count_abs a) = sa_priority a \<and>
   sa_wake (normalize_yield_count_abs a) = sa_wake a \<and>
   sa_event_waiting (normalize_yield_count_abs a) = sa_event_waiting a \<and>
   sa_ready (normalize_yield_count_abs a) = sa_ready a \<and>
   sa_delayed_a (normalize_yield_count_abs a) = sa_delayed_a a \<and>
   sa_delayed_b (normalize_yield_count_abs a) = sa_delayed_b a \<and>
   sa_current_role_a (normalize_yield_count_abs a) = sa_current_role_a a \<and>
   sa_pending (normalize_yield_count_abs a) = sa_pending a \<and>
   sa_suspended (normalize_yield_count_abs a) = sa_suspended a \<and>
   sa_tick (normalize_yield_count_abs a) = sa_tick a \<and>
   sa_missed_ticks (normalize_yield_count_abs a) = sa_missed_ticks a \<and>
   sa_suspend_depth (normalize_yield_count_abs a) = sa_suspend_depth a \<and>
   sa_missed_yield (normalize_yield_count_abs a) = sa_missed_yield a \<and>
   sa_top_ready (normalize_yield_count_abs a) = sa_top_ready a \<and>
   sa_current (normalize_yield_count_abs a) = sa_current a \<and>
   sa_overflows (normalize_yield_count_abs a) = sa_overflows a \<and>
   sa_yield_count (normalize_yield_count_abs a) =
     unat (of_nat (sa_yield_count a) :: 32 word)"
  by (simp add: normalize_yield_count_abs_def)

lemma normalize_yield_count_abs_idempotent [simp]:
  "normalize_yield_count_abs (normalize_yield_count_abs a) =
   normalize_yield_count_abs a"
  by (cases a) (simp add: normalize_yield_count_abs_def)

lemma scheduler_port_overlay_yield_count [simp]:
  "Scheduler_V611_Parse.globals.eal6_port_yield_count_'
      (scheduler_port_overlay depth irq_mask c) =
   Scheduler_V611_Parse.globals.eal6_port_yield_count_' c"
  by (simp add: scheduler_port_overlay_def)

lemma normalize_yield_count_abs_exactI:
  fixes w :: "32 word"
  assumes counter: "sa_yield_count a = unat w"
  shows
    "normalize_yield_count_abs a = a \<and>
     yield_count_mod_rel w (sa_yield_count a)"
proof -
  have normalized: "normalize_yield_count_abs a = a"
    using counter
    by (cases a) (simp add: normalize_yield_count_abs_def)
  have modular: "yield_count_mod_rel w (sa_yield_count a)"
    using counter by (simp add: yield_count_mod_rel_def)
  show ?thesis using normalized modular by blast
qed

lemma CursorGeneralStrongSchedulerEndpointRel_yield_countD:
  assumes endpoint:
    "CursorGeneralStrongSchedulerEndpointRel
       D c a managed termination external"
  shows
    "unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c) =
       sa_yield_count a"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using endpoint
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
qed

lemma CursorGeneralStrongSchedulerEndpointRel_modularI:
  assumes endpoint:
    "CursorGeneralStrongSchedulerEndpointRel
       D c a managed termination external"
  shows
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
proof -
  have counter:
    "sa_yield_count a =
       unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)"
    using CursorGeneralStrongSchedulerEndpointRel_yield_countD[OF endpoint]
    by simp
  note exact = normalize_yield_count_abs_exactI[OF counter]
  have normalized: "normalize_yield_count_abs a = a"
    using exact by blast
  have modular:
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
       (sa_yield_count a)"
    using exact by blast
  show ?thesis
    using endpoint normalized modular
    by (simp add: CursorGeneralStrongSchedulerModularEndpointRel_def)
qed

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_modularI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
proof -
  obtain c0 where overlay:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  have endpoint:
    "CursorGeneralStrongSchedulerEndpointRel
       D c0 a managed termination external"
    using public
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickPublicEntryRel_iff_endpoint_pending)
  have counter0:
    "sa_yield_count a =
       unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c0)"
    using CursorGeneralStrongSchedulerEndpointRel_yield_countD[OF endpoint]
    by simp
  have counter:
    "sa_yield_count a =
       unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)"
    using overlay counter0 by simp
  note exact = normalize_yield_count_abs_exactI[OF counter]
  have normalized: "normalize_yield_count_abs a = a"
    using exact by blast
  have modular:
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
       (sa_yield_count a)"
    using exact by blast
  show ?thesis
    using entry normalized modular
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
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

  val _ = audit_exact "yield-count normalization components" 0
    @{thm normalize_yield_count_abs_components}
  val _ = audit_exact "yield-count normalization idempotence" 0
    @{thm normalize_yield_count_abs_idempotent}
  val _ = audit_exact "proof-port overlay yield-count selector" 0
    @{thm scheduler_port_overlay_yield_count}
  val _ = audit_exact "exact yield-count normalization" 1
    @{thm normalize_yield_count_abs_exactI}
  val _ = audit_exact "exact endpoint yield count" 1
    @{thm CursorGeneralStrongSchedulerEndpointRel_yield_countD}
  val _ = audit_exact "exact endpoint to modular endpoint" 1
    @{thm CursorGeneralStrongSchedulerEndpointRel_modularI}
  val _ = audit_exact "exact protected entry to modular protected entry" 1
    @{thm CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_modularI}
\<close>

end
