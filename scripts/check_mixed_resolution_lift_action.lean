import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex

section NoModelStructure
variable {C : Type u} [Category.{v} C] {T : SSet.{v}}
  {A D : SimplexCategory ⥤ C} {B E : SimplexCategory ⥤ Cᵒᵖ}
example (a : CosimplicialMapFamily T D A) (b : CosimplicialMapFamily T E B)
    (t : T ⟶ MixedDiagonalHom.obj A B) :
    MixedDiagonalHom.pre a (MixedDiagonalHom.post b t) =
      MixedDiagonalHom.post b (MixedDiagonalHom.pre a t) := MixedDiagonalHom.pre_post a b t
end NoModelStructure

section ArbitraryModelSource
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := SerrePositivity.Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := SerrePositivity.Reedy.simplexModelCategory Cᵒᵖ

example : BiresolutionRawMapping.functor (C := C) ≅ MixedBiresolutionComparison.functor :=
  MixedBiresolutionComparison.rawIso
example {X X' : ResolutionObject C} (k : X ⟶ X') {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (MixedResolutionLiftAction.family X X' k.base (d ≫ ResolutionLiftSpace.ofLift k)).app n x =
      (DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation).app n.unop ≫
        k.diagram.app n.unop := MixedResolutionLiftAction.family_point k d n x

variable (X X' : ResolutionObject C) (f : X.base ⟶ X'.base)
  (Y Y' : ResolutionObject Cᵒᵖ) (g : Y.base ⟶ Y'.base)
example {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : T ⟶ MixedResolutionLiftAction.input X' Y') :
    MixedDiagonalHom.pre (MixedResolutionLiftAction.family X X' f s)
        (MixedDiagonalHom.post (MixedResolutionLiftAction.family Y Y' g r) t) =
      MixedDiagonalHom.post (MixedResolutionLiftAction.family Y Y' g r)
        (MixedDiagonalHom.pre (MixedResolutionLiftAction.family X X' f s) t) :=
  MixedResolutionLiftAction.action_orders X X' f Y Y' g s r t

-- Both old one-sided actions are recovered on the same full parameter maps.
example (Z : C) {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (t : T ⟶ (cosimplicialHom X'.resolution.obj).obj Z) :
    MixedDiagonalHom.pre (MixedResolutionLiftAction.family X X' f s)
        (t ≫ (MixedDiagonalHomRecovery.constantTargetIso X'.resolution.obj Z).inv) ≫
          (MixedDiagonalHomRecovery.constantTargetIso
            (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj) Z).hom =
      ResolutionLiftAction.parameterized X X' f Z s t :=
  MixedDiagonalHomRecovery.source_pairing _ _ _ (s ≫ ResolutionLiftSpace.inclusion X X' f) t
example (Z : C) {T : SSet.{v}} (r : T ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : T ⟶ MixedDiagonalHom.obj ((Functor.const SimplexCategory).obj Z) Y'.resolution.obj) :
    MixedDiagonalHom.post (MixedResolutionLiftAction.family Y Y' g r) t ≫
        (MixedDiagonalHomRecovery.constantSourceIso Z
          (DiagonalFrame.obj (ResolutionLiftSpace.frame Y).obj)).hom =
      ResolutionLiftAction.parameterized Y Y' g (op Z) r
        (t ≫ (MixedDiagonalHomRecovery.constantSourceIso Z Y'.resolution.obj).hom) :=
  MixedDiagonalHomRecovery.target_pairing _ _ _ (r ≫ ResolutionLiftSpace.inclusion Y Y' g) t

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
example {K L : SSet.{v}} (i : K ⟶ L) [Mono i]
    (s : K ⟶ ResolutionLiftSpace.obj X X' f) (r : K ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : L ⟶ MixedResolutionLiftAction.input X' Y') :
    ∃ (s' : L ⟶ ResolutionLiftSpace.obj X X' f) (r' : L ⟶ ResolutionLiftSpace.obj Y Y' g),
      i ≫ s' = s ∧ i ≫ r' = r ∧
        i ≫ MixedResolutionLiftAction.kanAction X X' f Y Y' g hcof hfib s' r' t =
          MixedResolutionLiftAction.kanAction X X' f Y Y' g hcof hfib s r (i ≫ t) :=
  MixedResolutionLiftAction.extends_kanAction X X' f Y Y' g hcof hfib i s r t
example : SSet.KanComplex ((SerrePositivity.SimplicialModel.KanReplacement.functor hcof hfib).obj
    (MixedResolutionLiftAction.output X Y)) :=
  SerrePositivity.SimplicialModel.KanReplacement.kanComplex hcof hfib _
end ArbitraryModelSource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialMapFamily,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalHom,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionLiftAction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedBiresolutionComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalHomRecovery]
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
  unless modules.size == expected.size do
    throwError "Some mixed resolution lift action modules were not audited"
  logInfo m!"Mixed resolution lift action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
