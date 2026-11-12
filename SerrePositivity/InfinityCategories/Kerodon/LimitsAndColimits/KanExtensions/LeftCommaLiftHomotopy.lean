module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyOppositeLaws
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaLift

/-!
概要：oriented comma への持ち上げから元の指定変換を厳密に回収する。
方針：反転前の comma の普遍変換の回収と、指定ホモトピーの二重反転を合成する。
規約：quasicategory 性と矢印の可逆性は不要。
使われ方：局所 Kan 添字の標準余錐と comma 内の図式を照合する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：指定変換の comma への持ち上げは普遍変換の制限として元の指定変換を回収する。
方針：反転前の持ち上げを普遍変換へ代入してから二重反転を戻す。
規約：実際の円柱の射が一致する。
使われ方：局所余錐の輸送の四境界の計算。 -/
lemma kanLeftCommaLift_homotopy_h {A K C : SSet.{u}} (δ : K ⟶ C)
    (a : A ⟶ K) (b : A ⟶ C) (H : SSet.Homotopy (a ≫ δ) b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLift δ a b H ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).h = H.h := by
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift (SSet.opFunctor.map δ) (SSet.opFunctor.map b) (SSet.opFunctor.map a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLiftOppositeHomotopy δ a b H)
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (SSet.opFunctor.map δ)))
  have hu : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp U l).h = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H).h := by
    change (l ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (SSet.opFunctor.map δ)))).h = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp, Category.comp_id]
    change (β_ A.op (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry l = _
    dsimp only [l]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_uncurry]
    simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    rfl
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp U l)).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H)).h := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite]
    rw [hu]
    rfl
  change (((SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map l) ▷
    (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite U).h ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom = _
  rw [comp_whiskerRight, Category.assoc]
  erw [← reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyOpposite_precomp_h U l), hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyOpposite_double_h H

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
