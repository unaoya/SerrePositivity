module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaRightPrism

/-!
概要：元の右向き全族と全円柱を、同じ元の図式 comma の入力へ戻す。
方針：対称な因子交換と内部 Hom の随伴、元の宇宙同型を合成する。
規約：元の C 全族と指定 D の全側面を厳密に保持する。
使われ方：slice 再構成から同じ元の diagram comma の全族を作る。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  {T : SSet.{u + 1}}
/-- 概要：元の右向き全射を図式の全族へ厳密に戻す。
方針：元の随伴と宇宙同型。規約：全射を保持。使われ方：元の comma への帰還。 -/
def diagramRightFamilyCurry
    (P : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj C) :
    T ⟶ (SSet.uliftFunctor.{u + 1, u}).obj ((ihom K).obj C) :=
  curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj K) T).hom ≫ P) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso K C).inv
/-- 概要：元の右向き全射を図式の全族へ厳密に戻す。
方針：元の随伴と宇宙同型。規約：全射を保持。使われ方：元の comma への帰還。 -/
def diagramRightPrismCurry
    (W : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :=
  curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T Δ[0])).hom ≫ W)
/-- 概要：元の右向き全射を図式の全族へ厳密に戻す。
方針：元の随伴と宇宙同型。規約：全射を保持。使われ方：元の comma への帰還。 -/
lemma diagramRightFamilyCurry_yoneda
    (P : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj C) :
    diagramRightFamilyCurry P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C =
      curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj K) T).hom ≫ P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) := by
  rw [diagramRightFamilyCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda, Category.assoc, Iso.inv_hom_id_assoc,
    ← curry_natural_right, Category.assoc]
/-- 概要：元の右向き全射を図式の全族へ厳密に戻す。
方針：元の随伴と宇宙同型。規約：全射を保持。使われ方：元の comma への帰還。 -/
lemma diagramRightPrismCurry_old
    (P : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj C)
    (W : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K) ≫ W = P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ≫ diagramRightPrismCurry κ W =
      diagramRightFamilyCurry P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C := by
  rw [diagramRightPrismCurry, ← curry_natural_left, ← Category.assoc,
    BraidedCategory.braiding_naturality_right, Category.assoc, h,
    diagramRightFamilyCurry_yoneda]
/-- 概要：元の右向き全射を図式の全族へ厳密に戻す。
方針：元の随伴と宇宙同型。規約：全射を保持。使われ方：元の comma への帰還。 -/
lemma diagramRightPrismCurry_tip
    (W : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K) ≫ W =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ≫ diagramRightPrismCurry κ W =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) := by
  rw [diagramRightPrismCurry, ← curry_natural_left, ← Category.assoc,
    BraidedCategory.braiding_naturality_right, Category.assoc, h,
    ← Category.assoc, braiding_hom_snd]
  apply uncurry_injective
  rw [uncurry_curry, SSet.yonedaEquiv_symm_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
