import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorCofibrant
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory SSet.{v} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C)

-- The actual enriched Hom isomorphism needs no model structure at all.
example : resolutionHom (tensorCosimplicialFamily S) (𝟭 C) ≅ eHomFunctor SSet.{v} C :=
  tensorHomBifunctorIso S

-- A natural isomorphism of the entire replaced bifunctors, not degreewise cardinalities.
example (Q R : C ⥤ C) :
    resolutionHom (Q ⋙ tensorCosimplicialFamily S) R ≅ enrichedReplacementHom Q R :=
  replacedTensorHomIso S Q R

-- The value is the existing enriched mapping object itself, with both replacements visible.
example (Q R : C ⥤ C) (X : Cᵒᵖ) (Y : C) :
    ((resolutionHom (Q ⋙ tensorCosimplicialFamily S) R).obj X).obj Y ≅
      (Q.obj X.unop ⟶[SSet.{v}] R.obj Y) :=
  ((replacedTensorHomIso S Q R).app X).app Y

example (X Y : C) (n : SimplexCategory) :
    (((tensorCosimplicialFamily S).obj X).obj n ⟶ Y) ≃
      (X ⟶[SSet.{v}] Y).obj (Opposite.op n) := simplexTensorHomEquiv S X Y n

-- The frame's actual Reedy cofibrancy follows from SM7, without assuming it separately.
example [ModelCategory C] [ModelCategory SSet.{v}] [IsQuillenBifunctor S.tensor]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (X : C) [IsCofibrant X] :
    reedyLeft simplex (cofibrations C) (Limits.initial.to ((tensorCosimplicialFamily S).obj X)) :=
  tensorCosimplicial_reedyCofibrant S hcof X

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorHom,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.StandardCosimplicial,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorCofibrant]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Simplicial tensor Hom comparison audit passed: {count} declarations in {seen.size} modules."
