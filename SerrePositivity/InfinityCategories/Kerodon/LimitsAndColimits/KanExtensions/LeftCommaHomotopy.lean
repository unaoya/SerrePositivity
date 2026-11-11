module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftComma
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingArrowFamilies

/-!
概要：反転した comma が表す δ(k)→c の指定自然変換と、既存の矢印空間への比較を構成する。
方針：comma の標準ホモトピーを反転し、二重反転の同型で標的を戻す。
規約：quasicategory 性は不要。
使われ方：cocartesian な置き換え上の構成から元の Kan 拡張の変換を取り出す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：oriented fiber product の二つの射影は δ(k)→c のホモトピーで結ばれる。
方針：反転した comma の標準ホモトピーを反転して標的を二重反転から戻す。
規約：可逆性は仮定せず、実際の矢印を保持する。
使われ方：元の添字と新しい cocartesian な射影の間の指定変換。 -/
def kanLeftCommaHomotopy {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (SSet.opFunctor.map δ))))
  refine {
    h := H.h ≫ (SSet.opFunctorCompOpFunctorIso.app C).hom
    h₀ := ?_
    h₁ := ?_
    rel := ?_ }
  · rw [← Category.assoc, H.h₀]
    change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget (SSet.opFunctor.map δ)) ≫
      SSet.opFunctor.map (SSet.opFunctor.map δ) ≫
        (SSet.opFunctorCompOpFunctorIso.app C).hom = _
    have hnat := SSet.opFunctorCompOpFunctorIso.hom.naturality δ
    change SSet.opFunctor.map (SSet.opFunctor.map δ) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom =
        (SSet.opFunctorCompOpFunctorIso.app K).hom ≫ δ at hnat
    rw [hnat]
    rfl
  · rw [← Category.assoc, H.h₁]
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：反転した comma のデータを既存の δ(k)→c の矢印空間へ写す。
方針：二つの射影と標準の指定ホモトピーを普遍性へ渡す。
規約：ここでは同型性を主張しない。
使われ方：既存の矢印の族の比較 API との接続。 -/
def kanLeftCommaToLeftMappingArrow {K C : SSet.{u}} (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftComma δ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow δ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ)
    (kanLeftCommaHomotopy δ)

/-- 概要：矢印空間への比較は元の添字への射影を保つ。
方針：矢印空間の持ち上げの射影公式。
規約：射の厳密な等式。
使われ方：元の図式の制限の比較。 -/
lemma kanLeftCommaToLeftMappingArrow_source {K C : SSet.{u}} (δ : K ⟶ C) :
    kanLeftCommaToLeftMappingArrow δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource δ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source _ _ _ _

/-- 概要：矢印空間への比較は底への射影を保つ。
方針：矢印空間の持ち上げの標的公式。
規約：射の厳密な等式。
使われ方：両表示の fiber ごとの図式の比較。 -/
lemma kanLeftCommaToLeftMappingArrow_projection {K C : SSet.{u}} (δ : K ⟶ C) :
    kanLeftCommaToLeftMappingArrow δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget δ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
