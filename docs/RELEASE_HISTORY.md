# Release history

This log starts with the first public release. Pre-publication development
milestones are not separate public versions.

## First public release (planned)

The release date and version tag will be recorded when the first public
release is published. This entry does not announce a release or tag.

- Formalization of the paper's four main theorems: 3.6, 3.8, 3.9, and 3.10,
  with finite, regular compact, and countable type models as specified in
  the linked Lean statements.
- An English [README](../README.md) with theorem locations and the minimal
  definitions needed to read their statements.
- Pinned Lean and mathlib v4.33.1 dependencies.
- Apache-2.0 licensing for the original repository source code, verification
  scripts, and documentation; third-party licenses remain unchanged.
- Windows and Unix verification entries. The console preserves native
  `#print axioms` messages for each distinct main-theorem implementation,
  using its actual fully qualified Lean name.
- A [verification record](VERIFICATION.md) that states the tests actually
  run and their coverage limits.

Future entries will describe changes relative to this public baseline.
