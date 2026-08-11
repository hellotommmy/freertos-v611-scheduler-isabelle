# Nested tick replay horizon and arithmetic bridge — 2026-08-11

Baseline: `174e5c98ba2a0330c0e4b6619b9408ad722673ae` on
`agent/universal-scheduler-refinement`.

## Checked scope

This staircase adds replay-horizon infrastructure only.  It does not execute,
instantiate, or prove the generated `whileLoop`.

The pure abstract child defines `resume_tick_arithmetic_defined_abs` as the
literal generated unlocked-tick arithmetic guard:

```isabelle
sa_tick a + 1 \<noteq> 0 \<or>
  (0 \<le> 2147483649 +
     sint (of_nat (sa_overflows a) :: 32 signed word) \<and>
   sint (of_nat (sa_overflows a) :: 32 signed word) < INT_MAX)
```

The explicit type is load-bearing: generated `xNumOfOverflows` is a
`32 signed word`.  The definition preserves the no-wrap/wrap-defined
disjunction and both literal signed guards.  It does not assume either branch
and does not replace the modular word observation by an unbounded integer.

`resume_missed_replay_horizon_safe` is recursive.  A horizon of `Suc n`
requires the current abstract guard and an `n`-step horizon from
`resume_missed_source_step_abs a`; horizon zero is true.  The checker proves:

1. `resume_missed_source_steps_abs (m+n) a` factors as the first `m` steps
   followed by `n` steps;
2. after any `n`, missed debt is exactly `sa_missed_ticks a - n` (natural
   truncated subtraction, with no `n <= debt` premise);
3. the recursive horizon is equivalent to the pointwise condition for every
   `i<n` abstract prefix state;
4. positive debt plus a full debt horizon yields the current abstract guard
   and the successor state's exact remaining-debt horizon.

The protected bridge child proves, from one arbitrary
`CursorGeneralStrongVTaskIncrementTickProtectedEntryRel` premise, the exact
scalar pins:

```isabelle
xTickCount_' c = sa_tick a
xNumOfOverflows_' c = of_nat (sa_overflows a)
unat (uxMissedTicks_' c) = sa_missed_ticks a
```

The proof first obtains the public shadow, extracts the Snapshot scalar
relation there, and only then transports the observations through the
arbitrary `depth`/`irq_mask` overlay.  It never unfolds PublicEntry directly on
the protected state.  The exported bridge is the single-premise equivalence:

```isabelle
generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
  resume_tick_arithmetic_defined_abs a
```

Protected entry and positive missed debt do not themselves imply either side.
In particular, the legal wrap state whose represented signed overflow word is
`INT_MAX` remains arithmetic-undefined; no no-wrap or overflow bound has been
introduced.

## Theorem-object audit

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `resume_missed_source_steps_abs_add` | 0 | 0 |
| `resume_missed_source_steps_abs_missed_ticks` | 0 | 0 |
| `resume_missed_replay_horizon_safe_iff` | 0 | 0 |
| `resume_missed_replay_horizon_safe_positive_shift` | 0 | 2 |
| `...ProtectedEntryRel_replay_scalar_pinsD` | 0 | 1 |
| `...ProtectedEntryRel_arithmetic_defined_iff` | 0 | 1 |

All task, priority, list, root, cursor, managed, termination, and external
parameters remain symbolic.  Managed and live domains remain distinct.

## Checker topology and staircase

Both exclusive child sessions set `document=false`,
`quick_and_dirty=false`, `parallel_proofs=0`, and session `timeout=60`.
Every command uses `-o quick_and_dirty=false -j 1`; the independent wrapper
bound is 300 seconds.

- `...Nested_Tick_Replay_Horizon_Abs` has sole parent
  `...Nested_Tick_Missed_Body_Capstone`, no side session, and its own theory
  directory.
- `...Nested_Tick_Replay_Arithmetic_Bridge` has sole parent the horizon child,
  no side session, and its own theory directory.

The abstract checker history was:

| run | exit | seconds | result |
| --- | ---: | ---: | --- |
| `20260811Tnested-tick-replay-horizon-abs-01` | 1 | 158.551 | zero-index branch needed its case equation |
| `...-02-zero-case` | 0 | 133.072 | provisional green; later bridge audit exposed an unsigned/signed cast mismatch |
| `...-03-signed-word` | 0 | 132.971 | final green with the exact signed-word literal guard; leaf 3 seconds |

The bridge first-error staircase was:

| run range | result |
| --- | --- |
| `...arithmetic-bridge-01` through `...-05-subst` | scalar extractor green; isolated the final high-order/conjunction rewrites and both overflow occurrences |
| `...-06-two-overflow-subst` through `...-10-blast` | both printed guards aligned, revealing the hidden `32 signed word` versus `32 word` type mismatch rather than a propositional failure |
| `...-11-signed-word` | exit 0, 142.523 seconds; final bridge leaf 2 seconds |

All fourteen recorded statuses have `quick_and_dirty=false` and
`timed_out=false`.  The red runs were proof/type localisation evidence and are
not accepted theorem evidence.

## Final green evidence hashes

### Abstract horizon — `20260811Tnested-tick-replay-horizon-abs-03-signed-word`

| object | SHA-256 |
| --- | --- |
| theory | `18D257D426E160B3D7ACB033D1B5B1CAD0BE746AB94712ECAB0A48777B6D0521` |
| `command.txt` | `30EC2F76B9831FED2182E5F952182DB77DD1BC4C0863BE20CECCE351BD7028F2` |
| `status.txt` | `DE073ACE277B52DB7E81662806B1931F0B7FF655FFE74D1CC5C5E75543AF0656` |
| `stdout.log` | `9DB1683A089F822DCD6BF8EDFF816F3490105200563547AF800052C94D54EA9E` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

### Protected bridge — `20260811Tnested-tick-replay-arithmetic-bridge-11-signed-word`

| object | SHA-256 |
| --- | --- |
| theory | `D9E8B6747B450661E844551298B7C1DF82124E122C3214664F157EF5CEBF1AC5` |
| `command.txt` | `32C38F0283F48F0C4D6DB62A1A5E0ABAECE5FB07CDD710A6508D7B24AB09D8B9` |
| `status.txt` | `EBEF7AD348468C913F332180B78C7B195E282143EEC34AAE80C41A1C4DBFC0C5` |
| `stdout.log` | `2B729D68DFDC7FE5CA2DF659F11D1B3DA53D219C1966568D5D51E66006368A17` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact open loop obligations

No safe replay loop theorem is claimed.  For the intended strengthened
relation

```isabelle
Rel c a \<longleftrightarrow>
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
    D depth irq_mask c a managed termination external \<and>
  sa_suspend_depth a = 0 \<and>
  resume_missed_replay_horizon_safe (sa_missed_ticks a) a
```

instantiating `resume_missed_generated_loop_replays` still requires these exact
named obligations:

```isabelle
step:
  \<And>c a. Rel c a \<Longrightarrow> 0 < sa_missed_ticks a \<Longrightarrow>
    resume_missed_generated_body () \<bullet> c
      \<lbrace>\<lambda>r t. r = Result () \<and>
        Rel t (resume_missed_source_step_abs a)\<rbrace>

count:
  \<And>c a. Rel c a \<Longrightarrow>
    unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
      sa_missed_ticks a
```

`count` is now a thin projection of the checked scalar extractor but has not
been packaged as the loop instantiation.  `step` still needs one named
connector combining: positive-horizon head/shift, the new arithmetic iff, the
already-green single-body theorem, and the abstract suspend-depth frame needed
to rebuild `Rel` at the successor.  Only after those two obligations and the
initial `Rel` are supplied may the existing generic replay-loop theorem be
instantiated.
