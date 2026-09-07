# Integration report — ext_def_3

Date: 2026-08-03

## Applied

| Item | Declaration | Target module | Action |
|------|-------------|---------------|--------|
| `items/ext_def_3.lean` | `IsWeakToWeakSequentiallyContinuous` | `Foundation/Hilbert/WeakConvergence.lean` | promote + recall |

- The definition was appended to `Foundation/Hilbert/WeakConvergence.lean` in the root namespace
  (file style), with a `/-! Source item: AttouchPeypouquetRedont2014 items/ext_def_3 -/` marker.
  No new imports were needed (the module already imports `Foundation.Hilbert.WeakTopology` and
  `Foundation.Topology.Sequences`).
- `items/ext_def_3.lean` is now a pure recall file:
  `recall IsWeakToWeakSequentiallyContinuous` (namespace wrapper dropped, matching the
  `Attouch_..._2020/items/ext_def_4.lean` convention).

## Users updated

None needed: `cor_1`, `prop_6`, `thm_1` use the bare name from inside
`namespace AttouchPeypouquetRedont2014`, which now resolves to the root Foundation declaration
via namespace backtracking. No fully-qualified references existed.

## Verification

- `lake build Foundation.Hilbert.WeakConvergence` — success (only pre-existing linter warnings).
- `lake env lean` on `items/ext_def_3.lean`, `items/cor_1.lean`, `items/prop_6.lean`,
  `items/thm_1.lean` — all exit 0.
- Full `lake build` — success (8315 jobs).
- Grep: no remaining `AttouchPeypouquetRedont2014.IsWeakToWeakSequentiallyContinuous` references.

## Follow-ups

None. (Note: `lake env lean` does not refresh imported oleans; use `lake build` after editing
`Foundation` modules before re-checking importers.)
