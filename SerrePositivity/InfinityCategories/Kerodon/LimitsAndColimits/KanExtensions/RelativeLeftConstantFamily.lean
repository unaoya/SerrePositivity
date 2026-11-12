module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeColimitConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical

/-!
概要：標準相対左 Kan 条件を定値パラメータ族へ移す。
方針：標準局所余錐の後合成を計算し、関手圏での相対余極限の保存を適用する。
規約：U の内部 Hom による後合成に関する相対条件を結論する。
使われ方：元の相対 Kan 関手の写像空間を全パラメータの Hom で比較する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準局所余錐は標的の関手による後合成と整合する。
方針：標準 slice の展開に合成の結合則を適用する。
規約：異なる図式上の余錐の値の厳密な等式。
使われ方：定値パラメータ族の標準相対 Kan 条件の同定。 -/
lemma kanLeftCanonicalCocone_postcomp_val {K C D E : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (U : D ⟶ E) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ (F ≫ U) c).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val ≫ U :=
  (Category.assoc _ _ _).symm

/-- 概要：標準相対左 Kan 拡張は定値パラメータ族への後合成で保たれる。
方針：各標準局所余錐を定値族へ写し、標準局所余錐との値の一致で比較する。
規約：δ やパラメータ A に単射性や quasicategory 性を要求しない。
使われ方：標準相対 Kan 条件を写像空間の全パラメータ判定に渡す。 -/
lemma kanIsRelativeLeftKanExtendedFrom_constantFamily {A K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) (F : C ⟶ D) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom ((ihom A).map U) δ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) := by
  intro c
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_constantFamily (A := A) U
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c) (hF c)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_congr ((ihom A).map U)
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram, Category.assoc])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeConstantFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c) A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) c)
    (kanLeftCanonicalCocone_postcomp_val δ F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) c).symm).1 hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
