# Nested tick missed-body capstone — 2026-08-11

Baseline: `0e530efd06f293c0b71cd29c1e6b0bd40e617921` on
`agent/universal-scheduler-refinement`.

## Checked scope

This staircase closes exactly one generated missed-replay body execution, in
source order:

1. `Scheduler_V611_Delay_Translation.vTaskIncrementTick'`;
2. `uxMissedTicks := uxMissedTicks - 1`.

The first exclusive child proves the cursor-general representation frame for
the second action.  It extracts the exact concrete missed count through
Snapshot, PublicEntry, and ProtectedEntry, proves a matching generic scalar
update, and specializes that update to the positive-debt word predecessor via
`Suc_unat_minus_one`.  The protected wrapper uses
`scheduler_port_overlay_missed_tick_update`; family witnesses, managed-domain
coverage, termination/external observations, delayed roots, and arbitrary
legal cursors are unchanged.

The second exclusive child composes that frame after the already-closed
protected generated tick transport.  Its main checked theorem is:

```isabelle
resume_missed_generated_body_protected_step:
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
    D depth irq_mask c a managed termination external \<Longrightarrow>
  sa_suspend_depth a = 0 \<Longrightarrow>
  0 < sa_missed_ticks a \<Longrightarrow>
  generated_unlocked_tick_arithmetic_defined c \<Longrightarrow>
  resume_missed_generated_body () \<bullet> c
    \<lbrace>\<lambda>r t. r = Result () \<and>
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
        D depth irq_mask t (resume_missed_source_step_abs a)
        managed termination external\<rbrace>
```

The four premises are deliberately retained in exactly that order: protected
entry, quiet scheduler, positive debt, and unlocked arithmetic definedness.
There is no no-wrap, task, priority, heap, list, pointer, cursor, source-success,
or termination premise.  `depth` and `irq_mask` remain arbitrary 32-bit words.
The sibling `resume_missed_generated_body_protected_step_1_1` specializes only
the two proof-port words to `1/1` and retains the same four premises.

The checked ML theorem-object audit is:

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `resume_missed_generated_body_protected_step` | 0 | 4 |
| `resume_missed_generated_body_protected_step_1_1` | 0 | 4 |

Managed and live domains remain distinct.  Concrete word subtraction remains
modular; positivity is used only to relate the nonzero word predecessor to the
natural-number abstract debt.  The generated tick is not reopened, and its
guard-failure and arithmetic-defined boundary are not weakened.

## Checker topology and staircase

Both sessions set `document=false`, `quick_and_dirty=false`,
`parallel_proofs=0`, and Isabelle session `timeout=60`; every checker command
uses `-o quick_and_dirty=false -j 1`.  The wrapper bound is 300 seconds and is
reported separately from the session bound.

- `...Nested_Tick_Missed_Decrement_Frame` has sole parent
  `...Nested_Tick_Overlay_Capstone` and no side session.
- `...Nested_Tick_Missed_Body_Capstone` has sole parent the decrement-frame
  child.  Its only side sessions are `...Resume_Generated_Missed_Loop`, which
  exposes the exact generated body/source-step factors, and the minimal
  `...Resume_Missed_Tick_Replay_Frame`, which exports
  `tick_unlocked_frames_missed_ticks`.

The decrement-frame runs followed first-error discipline:

| run | exit | seconds | first checked boundary |
| --- | ---: | ---: | --- |
| `20260811Tnested-tick-missed-decrement-frame-01` | 1 | 137.029 | generic current-state selector frame |
| `...-02-current` | 1 | 125.507 | Snapshot simplifier bypassed the generic frame |
| `...-03-snapshot-current` | 1 | 200.598 | Entry wrapper needed explicit update/count instantiation |
| `...-04-entry-inst` | 1 | 128.832 | Public wrapper needed the same explicit instantiation |
| `...-05-public-inst` | 1 | 127.839 | Protected wrapper needed the same explicit instantiation |
| `...-06-protected-inst` | 1 | 127.213 | final decrement corollary needed the exact lambda/count instance |
| `...-07-green` | 0 | 128.969 | green; leaf finished in 3 seconds |

The body runs were:

| run | exit | seconds | result |
| --- | ---: | ---: | --- |
| `20260811Tnested-tick-missed-body-capstone-01` | 1 | 152.219 | local meta-bound tail needed an explicit proposition |
| `...-02-explicit-tail` | 0 | 140.387 | green; leaf finished in 13 seconds |

Every listed run records `quick_and_dirty=false` and `timed_out=false`.

## Green evidence hashes

### Decrement frame — `20260811Tnested-tick-missed-decrement-frame-07-green`

| object | SHA-256 |
| --- | --- |
| theory | `E8BD30B2A51F92132831C61E4BB9F7755CD9829F677FBDC9FAC32588668101F1` |
| `command.txt` | `10AAAFEDCDBC57793334D4B04C5651FDF90E7CCA468B3ADA3B1A786E98AFB81A` |
| `status.txt` | `B97AC85E2E64C29D8CDCBDBF28A5F413B774DB62EEE234879807515D1B07D8B0` |
| `stdout.log` | `EF349822BB1BFC02C1FD71E760583E2B7E702FBA9A2FA86264E4CAB8CE8F4996` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

### Body capstone — `20260811Tnested-tick-missed-body-capstone-02-explicit-tail`

| object | SHA-256 |
| --- | --- |
| theory | `28EBF38749573C830CC33B6E1CA22EB46F9BC7745B02A25D5371DC6073FEEEFC` |
| `command.txt` | `D6689827C34D4F9A204D5EA50AB4B16D57890D31C591EB66990196515C5B24C1` |
| `status.txt` | `9695C6D668B39F6FAF5287BA203E8EE49A0E091481968127D27473B1C7FAFAD1` |
| `stdout.log` | `35D8AAE93B1E07556C66FC1D97DAAF1B0D0A5AFC12BB0CF6143BDC69A5672AB6` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact next boundary

No `whileLoop`, replay horizon, or whole-resume theorem is proved here.  The
first remaining semantic rule is the replay-horizon/stability connector that
supplies `generated_unlocked_tick_arithmetic_defined` at every positive-debt
protected replay state (while preserving the quiet scheduler and protected
relation).  Only after that rule is available can the checked single-body step
and missed-count extractor discharge the open `step` and `count` premises of
`resume_missed_generated_loop_replays`.
