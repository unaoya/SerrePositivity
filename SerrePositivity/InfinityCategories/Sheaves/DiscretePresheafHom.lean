module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYoneda
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：元の離散前層埋め込みによる射を、同じ指定頂点の間の Hom として読む。
方針：元の辺を送り、頂点の仕様の等式だけで端点を正規化する。
規約：HTT 5.5.6.28 の集合値前層の特殊な表示。新しい辺を選択しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 元の離散埋め込みによる同じ辺を、指定された二つの前層の間の Hom に正規化する。 -/
@[cite HTT "5.5.6.28" (partial := special) "小さい通常siteの集合値前層の離散埋め込みのHom作用。"]
def discretePresheafHom (φ : P ⟶ Q) :
    FunctorHom (discretePresheaf P) (discretePresheaf Q) :=
  Truncated.HomotopyCategory.homMk
    ((((nerve.edgeMk φ).map (discretePresheafInclusion C).val).ofEq
      ((discretePresheafInclusion C).property.1 P)
      ((discretePresheafInclusion C).property.1 Q)).toTruncated)

/-- 正規化は、元の辺の類への頂点の等式の前後合成そのもの。 -/
lemma discretePresheafHom_eq_normalized (φ : P ⟶ Q) :
    discretePresheafHom φ =
      eqToHom (congrArg HomotopyCategory.mk ((discretePresheafInclusion C).property.1 P).symm) ≫
      Truncated.HomotopyCategory.homMk
        (((nerve.edgeMk φ).map (discretePresheafInclusion C).val).toTruncated) ≫
      eqToHom (congrArg HomotopyCategory.mk ((discretePresheafInclusion C).property.1 Q)) := by
  exact homMk_edge_ofEq _ _ _
end SerrePositivity.InfinityCategories.Sheaves
