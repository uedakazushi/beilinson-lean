# Optional Axiom Stacks integration (2026-11-07)

This is an **experimental, separate Lake project** to check compatibility and discover reusable Stacks declarations. It intentionally does NOT install the enormous Stacks dependency in the default Verso/Beilinson project.

- Upstream: https://github.com/AxiomMath/Stacks
- Revision: `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` (2026-11-06)
- Stacks toolchain at this revision: Lean v4.35.0
- Its mathlib dependency: v4.35.0
- Upstream code has human-reviewed `StacksCore` and AI-generated, kernel-checked `StacksFrontier`.
- README and website documentation: https://stacks.axiommath.ai/

From this directory:

```sh
lake update
lake exe cache get
lake build StacksProbe
```

The build has **not been run yet**. Stacks has tens of thousands of modules, and its upstream README warns that a full build is expensive without a compiled-object cache. Do not automatically run `lake build Stacks` or `import Stacks` in the main project. The proof probe currently imports the published module `StacksFrontier.AlgebraicGeometry.AffineDerivedBaseChange`, but this import has not been elaborated locally.

If the build succeeds, commit the generated **integration-specific** `lake-manifest.json` inside `integrations/stacks/`. Do not copy it into the root Lake project. The probe alone is not evidence that any Beilinson prerequisite is already supplied.

To use a particular Stacks theorem in the production Beilinson library, first record its tag, Lean declaration, assumptions, exact module, tier and semantic audit in `REUSE.md`. Only then choose whether to promote Stacks to a direct dependency, add a small adapter, or re-use the result indirectly through mathlib. Do not duplicate it by default.
