module
public import Mathlib.CategoryTheory.Limits.Preorder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.Tactic.CrossRefAttribute

/-!
標準単体の最初の頂点の包含。Kerodon 4.2.4.11（Tag 05HX）。

対応節は Kerodon 4.2（Tag 014H）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open _root_.SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 概要：標準単体の最初の頂点の包含は left anodyne。
方針：有限順序圏の始対象の nerve 包含を標準単体の同型で移す。
規約：次数 n は任意。使われ方：基底の余錐を最初の辺から選ぶ。 -/
@[kerodon 05HX]
lemma stdSimplex_firstVertex_leftAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (SSet.yonedaEquiv.symm
      (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne (Preorder.isInitialBot (ULift.{u} (Fin (n + 1))))
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ (stdSimplex.isoNerve n).inv h
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions _)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (⊥ : ULift.{u} (Fin (n + 1))) ≫ (stdSimplex.isoNerve n).inv =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) := by
    apply (cancel_mono (stdSimplex.isoNerve n).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply SSet.yonedaEquiv.injective
    rfl
  exact he ▸ hh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
