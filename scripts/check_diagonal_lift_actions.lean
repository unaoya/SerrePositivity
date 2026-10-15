import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

-- Actual simplicial composition, with no model structure or enrichment on C.
example {C : Type u} [Category.{v} C]
    (A : SimplexCategory ⥤ SimplexCategory ⥤ C) (B : SimplexCategory ⥤ C) (Z : C) :
    (cosimplicialHom A).obj B ⨯ (cosimplicialHom B).obj Z ⟶
      (cosimplicialHom (DiagonalFrame.obj A)).obj Z :=
  DiagonalHom.composition A B Z

-- The full lift space acts, not just pi zero or points in Ho(SSet).
example {C : Type u} [Category.{v} C] [ModelCategory C]
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) :
    ResolutionLiftSpace.obj X Y f ⨯ (cosimplicialHom Y.resolution.obj).obj Z ⟶
      ResolutionLiftAction.target X Z := ResolutionLiftAction.action X Y f Z

-- At any actual lift the formula is exactly the old Hom map and comparison.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    {X Y : ResolutionObject C} (f : X ⟶ Y) (Z : C) {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (t : T ⟶ (cosimplicialHom Y.resolution.obj).obj Z) :
    ResolutionLiftAction.parameterized X Y f.base Z (d ≫ ResolutionLiftSpace.ofLift f) t =
      t ≫ (cosimplicialHomMap f.diagram).app Z ≫ ResolutionLiftAction.comparison X Z :=
  ResolutionLiftAction.ofLift f Z d t

-- Every higher boundary action extends, preserving the given boundary.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) (n : ℕ)
    (b : (SSet.boundary.{v} n).toSSet ⟶ ResolutionLiftSpace.obj X Y f)
    (t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (cosimplicialHom Y.resolution.obj).obj Z) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ ResolutionLiftSpace.obj X Y f,
      (SSet.boundary n).ι ≫ e = b ∧
      (SSet.boundary n).ι ≫ ResolutionLiftAction.parameterized X Y f Z e t =
        ResolutionLiftAction.parameterized X Y f Z b ((SSet.boundary n).ι ≫ t) :=
  ResolutionLiftAction.extends_action hcof X Y f Z _ b t

-- Rowwise weak equivalences use only the arbitrary source model, with no
-- specified functorial factorization, presentability or enriched structure.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (X : ResolutionObject C) (Z : C) [IsFibrant Z] (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v} ((ResolutionLiftAction.rowComparison X Z).app n) :=
  ResolutionLiftAction.rowComparison_weakEquivalence hcof X Z n

-- The diagonal's augmentation is degreewise weak; this does not assert that
-- the induced diagonal mapping-space comparison is already a weak equivalence.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    (B : SimplexCategory ⥤ C) (n : SimplexCategory) :
    weakEquivalences C ((DiagonalFrame.resolutionAugmentation B).app n) :=
  DiagonalFrame.resolutionAugmentation_weakEquivalence B n

-- The exact row-diagonal comparison is the original augmentation Hom map.
-- Thus a future bisimplicial diagonal theorem will apply to this very map.
example {C : Type u} [Category.{v} C]
    {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C) :
    (DiagonalFrame.constantIso ((cosimplicialHom B).obj Z)).inv ≫
      DiagonalFrame.map (DiagonalMappingRows.comparison a Z) ≫
        (DiagonalMappingComparison.iso A Z).hom =
          (cosimplicialHomMap (DiagonalFrame.augmentation a)).app Z :=
  DiagonalMappingComparison.comparison_eq a Z

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingRows,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction]
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
  unless modules.size == expected.size do throwError "Some diagonal lift action modules were not audited"
  logInfo m!"Diagonal lift action audit passed: {count} declarations in {modules.size} modules, standard axioms only."
