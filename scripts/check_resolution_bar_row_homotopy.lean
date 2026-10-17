import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v uD vD uB vB u vH uH
noncomputable section
open CategoryTheory
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- The full homotopy uses independent source, value, and base universes, without any model.
example {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
    (p : D ⥤ B) (F : D ⥤ SSet.{v}) {b : B} {d e : D}
    (α : p.obj d ⟶ b) (β : p.obj e ⟶ b) (k : d ⟶ e) (hk : p.map k ≫ β = α) :
    SSet.Homotopy (BarConstruction.commaSection p F α)
      (UniverseLift.map.{max uD vD vB} (F.map k) ≫ BarConstruction.commaSection p F β) :=
  BarConstruction.commaSectionHomotopy p F α β k hk

-- The actual right leg, not an independently selected comparison, is detected on its section.
example {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
    (p : D ⥤ B) (F : D ⥤ SSet.{v}) {H : Type uH} [Category.{vH} H]
    (L : SSet.{max uD vD v vB} ⥤ H) (hL : SSet.anodyneExtensions.IsInvertedBy L) (d : D) :
    IsIso (L.map ((BarConstruction.spanRight p F).app d)) ↔
      IsIso (L.map (BarConstruction.commaSection p F (𝟙 (p.obj d)))) :=
  BarConstruction.spanRight_isIso_iff_section p F L hL d

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ)

-- The original reference map from the previous bar evaluation is retained after padding.
example : (UniverseLift.paddingIso.{v, u}.app
      ((MixedBiresolutionComparison.functor (C := C)).obj R)).hom ≫
    BarConstruction.commaSection (RightResolutionMapping.projection (C := C))
      MixedBiresolutionComparison.functor (𝟙 ((RightResolutionMapping.projection (C := C)).obj R)) =
      ResolutionBarReference.sectionMap R :=
  ResolutionBarRowHomotopy.padded_reference R

example : SSet.Homotopy (ResolutionBarReference.sectionMap R)
    (UniverseLift.map.{u} ((ResolutionRowMixedMapping.rowComparison n).app R) ≫
      ResolutionBarRowHomotopy.sectionMap R n) :=
  ResolutionBarRowHomotopy.homotopy R n

variable [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- This is a reduction to the row section; it does not assert either side is already invertible.
example : IsIso (AnodyneHomotopy.anodyneQ.map
    ((BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
      MixedBiresolutionComparison.functor).app R)) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (ResolutionBarRowHomotopy.sectionMap R n)) :=
  ResolutionBarRowHomotopy.right_isIso_iff_row R n hcof hfib

example : IsIso (Functor.whiskerRight
    (BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
      MixedBiresolutionComparison.functor) AnodyneHomotopy.anodyneQ) ↔
    ∀ R' : RightResolutionMapping.Index C, IsIso (AnodyneHomotopy.anodyneQ.map
      (ResolutionBarRowHomotopy.sectionMap R' (Opposite.op (SimplexCategory.mk 0)))) :=
  ResolutionBarRowHomotopy.natural_right_isIso_iff_rows hcof hfib

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSections,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftPadding,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowHomotopy]
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
    throwError "Some resolution bar row homotopy modules were not audited"
  logInfo m!"Resolution bar row homotopy audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
