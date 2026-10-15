import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyLimit
import Lean.Util.CollectAxioms

noncomputable section
universe w vH uH vD uD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

variable (K : Type w) [SmallCategory K]

-- The ordinary weighted adjunction does not require any model existence.
example (W : K ⥤ SSet.{w}) :
    WeightedCones.tensorDiagram K W ⊣ WeightedCones.coneSpace K W :=
  WeightedCones.adjunction K W

example : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

-- The consumer supplies only the explicit mono/Kan classes on an existing
-- simplicial model. Boundary/horn generation and the tensor Quillen condition
-- are proved inputs, not extra diagram-model or holim assumptions.
example {F G : K ⥤ SSet.{w}} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences SSet.{w} (f.app k)) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    weakEquivalences SSet.{w}
      ((HomotopyLimit.functor K SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J).map f) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  have := SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  exact HomotopyLimit.map_weakEquivalence K _ _ f hf

example (F : K ⥤ SSet.{w}) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    IsFibrant ((HomotopyLimit.functor K
      SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J).obj F) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  have := SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  exact HomotopyCones.isFibrant K _ _ F

-- Every ordinary localization, in independent output universes, receives
-- the actual holim computation and a constructed right adjoint of the
-- canonical descended constant functor. No prechosen derived functors input.
example {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
    (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})]
    (Q : (K ⥤ SSet.{w}) ⥤ D)
    [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w}))] :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    ∃ RF : D ⥤ H, Nonempty (HomotopyLimit.localizedConstant K L Q ⊣ RF) ∧
      Nonempty (HomotopyLimit.functor K SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J ⋙ L ≅ Q ⋙ RF) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  have := SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  exact HomotopyLimit.exists_localizedAdjunction K L Q _ _ hcof

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyCones,
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightComparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.DerivedConstantAdjunction,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyLimit]
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
  logInfo m!"Actual homotopy limit audit passed: {count} declarations in {seen.size} modules."
