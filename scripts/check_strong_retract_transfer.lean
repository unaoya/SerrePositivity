import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- Neither the generic map nor its source and target need a model structure or Kan condition.
example {E B : SSet.{w}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{w}).rlp p) (s : B ⟶ E)
    (hs : s ≫ p = 𝟙 B) :
    ∃ H : SSet.Homotopy (𝟙 E) (p ≫ s),
      H.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p ∧
      s ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
        fst B (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ s :=
  MonoRightLiftingRelativeHomotopy.exists_strong_contraction p hp s hs

-- Both endpoints, the entire subobject homotopy, and the entire projection are retained.
example {E B X Y : SSet.{w}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{w}).rlp p) (i : X ⟶ Y) [Mono i]
    {f g : Y ⟶ E} (H : SSet.Homotopy f g) (A : SSet.Homotopy (i ≫ f) (i ≫ g))
    (ha : A.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h ≫ p) :
    ∃ V : SSet.Homotopy f g, V.h ≫ p = H.h ≫ p ∧
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = A.h :=
  MonoRightLiftingRelativeHomotopy.exists_extension p hp i H A ha

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- The normalization survives precomposition by an arbitrary large parameter object.
example (b : Cᵒᵖ × C) {T : SSet.{max u v}}
    (a : T ⟶ OrdinaryBarRetractSystem.lifted hcof hfib b) :
    (a ≫ OrdinaryBarRetractSystem.section_ hcof hfib b) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (OrdinaryBarRetractSystem.contraction hcof hfib b).h =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ a ≫
        OrdinaryBarRetractSystem.section_ hcof hfib b :=
  OrdinaryBarRetractSystem.contraction_pre_section hcof hfib b a

example (b : Cᵒᵖ × C) :
    OrdinaryBarRetractSystem.smallTransferArrow hcof hfib
      (𝟙 (OrdinaryBarRetractSystem.ambient hcof hfib b)) =
        𝟙 (OrdinaryBarRetractSystem.small hcof hfib b) :=
  OrdinaryBarRetractSystem.smallTransferArrow_id hcof hfib b

-- The entire comparison interval is constant, not just its homotopy class or endpoints.
example {b c : Cᵒᵖ × C}
    (a : OrdinaryBarRetractSystem.ambient hcof hfib b ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib c) :
    (OrdinaryBarRetractSystem.smallTransferCompositionHomotopy hcof hfib (𝟙 _) a).h =
      fst (OrdinaryBarRetractSystem.small hcof hfib b)
        (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        OrdinaryBarRetractSystem.smallTransferArrow hcof hfib a :=
  OrdinaryBarRetractSystem.smallTransferCompositionHomotopy_left_id hcof hfib a

example {b c : Cᵒᵖ × C}
    (a : OrdinaryBarRetractSystem.ambient hcof hfib b ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib c) :
    (OrdinaryBarRetractSystem.smallTransferCompositionHomotopy hcof hfib a (𝟙 _)).h =
      fst (OrdinaryBarRetractSystem.small hcof hfib b)
        (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        OrdinaryBarRetractSystem.smallTransferArrow hcof hfib a :=
  OrdinaryBarRetractSystem.smallTransferCompositionHomotopy_right_id hcof hfib a
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem]
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
    throwError "Missing strong retract transfer modules"
  logInfo m!"Strong retract transfer audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
