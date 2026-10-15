import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe vC uC vD uD vHC uHC vHD uHD
noncomputable section
open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen

-- Independent source, target and localization universes; no functorial
-- factorizations, simplicial structure, or model generation data are assumed.
example {C : Type uC} [Category.{vC} C] [ModelCategory C]
    {D : Type uD} [Category.{vD} D] [ModelCategory D]
    {HC : Type uHC} [Category.{vHC} HC] {HD : Type uHD} [Category.{vHD} HD]
    (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
    (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]
    (F : C ⥤ D) [F.IsLeftAdjoint] [IsLeftQuillen F]
    (G : D ⥤ C) [G.IsLeftAdjoint] [IsLeftQuillen G]
    (LF : HC ⥤ HD) (LG : HD ⥤ HC)
    (α : QC ⋙ LF ⟶ F ⋙ QD) [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
    (β : QD ⋙ LG ⟶ G ⋙ QC) [LG.IsLeftDerivedFunctor β (weakEquivalences D)]
    (ε : F ⋙ G ⟶ 𝟭 C) (δ : G ⋙ F ⟶ 𝟭 D)
    (hε : ∀ (X : C), IsCofibrant X → WeakEquivalence (ε.app X))
    (hδ : ∀ (Y : D), IsCofibrant Y → WeakEquivalence (δ.app Y)) :
    ∃ e : HC ≌ HD, e.functor = LF ∧ e.inverse = LG :=
  ⟨derivedWeakInverseEquivalence QC QD α β ε δ hε hδ, rfl, rfl⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedComposition,
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedWeakInverse,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.DerivedTensorInverse]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do throwError "Some derived weak inverse modules were not audited"
  logInfo m!"Derived weak inverse audit passed: {count} declarations in {modules.size} modules, standard axioms only."
