# Build provenance

## Protected two-paper preflight: 2026-11-04

Both Palomar entries passed at release commit
`ccbba1356d6e737e1e7dd336a7014360e2f52251`, using Lean 4.35.0 and
Mathlib v4.35.0. Comparator, Lean, NanoDa, and con-ron accepted the selected
declarations; both mechanical reports contain no errors or warnings.

- [Verification run and reports](https://github.com/what-social-construct/jacobian-collision-geometry/actions/runs/41967486280)
- [Exact submission paths and scope](CollisionIdeals/Palomar/README.md)

This evidence applies to the immutable release above, not to later commits.
The main development uses Lean 4.28.0 and Mathlib v4.28.0. Neither a local
build nor a protected preflight constitutes Palomar registration.

## Historical full-development build: 2026-07-30

The following record is retained in place for historical provenance. Its
Lean 4.24.0 toolchain and source commit are not the current submission.

- Result: **success** (`lake build` exited with code `0`)
- Lake report: `Build completed successfully (2726 jobs).`
- Verification window (UTC): `2026-07-30T14:12:04Z`–`2026-07-30T14:13:17Z`
- Repository branch: `main`, synchronized with `origin/main`
- Source commit: `a409db9922279907493d96f691b5ea9eb71baaf9`
- Source tree: `4bef60d8e1c44c8069d3836f983e0f73af321eab`
- Working tree during verification: clean
- Declared toolchain: `leanprover/lean4:v4.24.0`
- Lean runtime: `Lean (version 4.24.0, arm64-apple-darwin23.6.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)`
- Lake runtime: `Lake version 5.0.0-src+797c613 (Lean version 4.24.0)`
- Mathlib revision: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

The verification command was:

```text
lake build
```

This record identifies the committed source tree above. The record itself was
created after that build, so it becomes part of the repository's history only
when it is committed (and, for a public timestamp, pushed or otherwise
externally anchored).
