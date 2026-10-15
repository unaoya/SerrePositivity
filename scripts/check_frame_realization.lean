import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomRealization
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vH uH
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

section Ordinary
variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{0, v} C]

-- This is an actual adjunction in the existing categories, with no model input.
example (A : SimplexCategory ⥤ C) : Realization.functor A ⊣ cosimplicialHom A :=
  Realization.adjunction A

example (A : SimplexCategory ⥤ C) : A ≅ uliftYoneda.{v,0,0} ⋙ Realization.functor A :=
  Realization.representableIso A

example {A B : SimplexCategory ⥤ C} (a : A ⟶ B) :
    a ≫ Realization.unit B = Realization.unit A ≫
      Functor.whiskerLeft uliftYoneda.{v,0,0} (Realization.family.map a) :=
  Realization.unit_naturality a
end Ordinary

section Presentable
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

-- The presentability universe, Hom universe and object universe are independent.
-- No v-sized colimits are assumed in this section.
example (A : SimplexCategory ⥤ C) :
    SmallHomRealization.functor.{w} A ⊣ SmallHomRealization.hom.{w} A :=
  SmallHomRealization.adjunction A

example (A : SimplexCategory ⥤ C) :
    SmallHomRealization.hom.{w} A ⋙ SSet.uliftFunctor.{v,w} ≅
      cosimplicialHom A ⋙ SSet.uliftFunctor.{w,v} := SmallHomRealization.homLiftIso A

example :
    (SerrePositivity.SmallHomModel.modelCategory.{w} C).categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences C).inverseImage (SerrePositivity.SmallHomModel.equivalence.{w} C).functor :=
  SerrePositivity.SmallHomModel.modelCategory_weakEquivalences C

variable [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

-- Cofibrancy and constancy of the frame suffice, without source tensor,
-- enrichment, chosen factorization data or an equality of universe levels.
example : SerrePositivity.Quillen.IsLeftQuillen (SmallHomRealization.functor.{w} A) :=
  SmallHomRealization.isLeftQuillen hcof hfib A hA hconst

example : SerrePositivity.Quillen.IsRightQuillen (SmallHomRealization.hom.{w} A) :=
  SmallHomRealization.isRightQuillen hcof hfib A hA hconst

example {H : Type uH} [Category.{vH} H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] :
    (SmallHomRealization.functor.{w} A ⋙ L).HasPointwiseLeftDerivedFunctor
      (weakEquivalences SSet.{w}) :=
  SmallHomRealization.hasPointwiseLeftDerived hcof hfib A hA hconst L
end Presentable

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.SmallHomModel,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Realization,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomRealization]
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
  logInfo m!"Frame realization and small Hom model audit passed: {count} declarations in {seen.size} modules."
