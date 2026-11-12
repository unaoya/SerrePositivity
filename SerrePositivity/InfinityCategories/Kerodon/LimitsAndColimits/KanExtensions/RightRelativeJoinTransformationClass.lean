module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightRelativeJoinCorrectionSquares

/-!
概要：相対 join の厳密化が指定自然変換の h Fun の類を保存することを証明する。
方針：両補正正方形の側辺の類を比較し、可逆な左辺を消去する。
規約：端点同型の代表の選び直しは、raw な等式ではなく Arrow の類の等式で扱う。
使われ方：指定変換を保った相対 join への還元。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：円柱比較と厳密化の正方形の左辺は同じ h Fun の射を表す。
方針：両端の同時の比較の類を左端へ制限し、各側辺の raw な表示を使う。
規約：両側辺の代表そのものの一致は要求しない。
使われ方：正方形による上辺の類の比較。 -/
lemma RightKanRelativeJoinRealization.Strictification.leftBoundary_hom_eq
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation α s.comparisonPrismHomotopy)) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp s.endpointsIso.simplicialHomotopy (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K))
    r.correctionSquare_left_h
  have hb := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation α s.comparisonPrismHomotopy)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp s.comparison.simplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderEndpointInclusion δ)) (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K)) (by
      change _ = ((δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K) ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderEndpointInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ _
      rw [s.comparisonSquare_left_h, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
      rfl)
  have hm := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_precomp_hom_arrow _ _ s.endpointsHomotopy_hom_arrow
    (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K)
  apply Arrow.mk_injective _ _
  exact hb.trans (hm.symm.trans hc.symm)

/-- 概要：円柱比較と厳密化の正方形の右辺は同じ h Fun の射を表す。
方針：両端の同時の比較の類を右端へ制限する。
規約：右辺の始域は K。
使われ方：二つの上辺の類の同定。 -/
lemma RightKanRelativeJoinRealization.Strictification.rightBoundary_hom_eq
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation α s.comparisonPrismHomotopy)) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation r.transformation
        r.correctionPrismHomotopy)) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation r.transformation r.correctionPrismHomotopy)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp s.endpointsIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K))
    r.correctionSquare_right_h
  have hb := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation α s.comparisonPrismHomotopy)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp s.comparison.simplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderEndpointInclusion δ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K)) (by
      change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderEndpointInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ _
      rw [s.comparisonSquare_right_h, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
      rfl)
  have hm := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_precomp_hom_arrow _ _ s.endpointsHomotopy_hom_arrow
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K)
  apply Arrow.mk_injective _ _
  exact hb.trans (hm.symm.trans hc.symm)

/-- 概要：厳密化の補正正方形の左辺は可逆。
方針：両端同型の代表の前合成の類は同型の射の前合成である。
規約：別の同型の代表を左辺として選び直さない。
使われ方：h Fun 内で左辺を消去する。 -/
lemma RightKanRelativeJoinRealization.Strictification.leftBoundary_invertible
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp s.endpointsIso.simplicialHomotopy (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    dsimp only [H]
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom]
    infer_instance
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ?_).2 hi
  change SSet.yonedaEquiv (curry _) = SSet.yonedaEquiv (curry H.h)
  rw [r.correctionSquare_left_h]
  rfl

/-- 概要：相対 join の端点の厳密化は指定自然変換の h Fun の類を保存する。
方針：共通の下辺を持つ二つの補正正方形で側辺の類を比較し、左の同型を消去する。
規約：δ の単射性は不要。元の α そのものとの raw な等式は主張しない。
使われ方：元の指定変換を保って Kerodon Proposition 7.3.6.1（Tag 0309） の相対 join 表示へ移る。 -/
lemma RightKanRelativeJoinRealization.Strictification.transformation_hom_eq
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.transformation) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomSquare_top_hom_eq_of_boundary_classes r.correctionSquare s.comparisonSquare
    r.leftBoundary_hom_eq.symm r.rightBoundary_hom_eq.symm r.leftBoundary_invertible

/-- 概要：端点の厳密化前後で、元の指定変換に関する右 Kan 条件は同値。
方針：指定変換の類の保存を、既存の右 Kan 条件の h 不変性へ渡す。
規約：右 Kan 条件を追加仮定として厳密化データに組み込まない。
使われ方：相対 join 上の図式を用いる大域的普遍性の証明への接続。 -/
lemma RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F r.transformation ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isRightKanExtension_iff_of_homMk_eq δ F₀ F r.transformation α r.transformation_hom_eq

/-- 概要：任意の指定自然変換は、同じ h Fun の類を持つ相対 join の prism で表示できる。
方針：円柱比較の存在、両端の厳密化、変換の類の保存を合成する。
規約：δ の単射性は不要。両端は元の図式に厳密に等しい。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の相対 join への還元。 -/
lemma rightKanRelativeJoin_realization_preserving_class {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α : SSet.Homotopy (δ ≫ F) F₀) :
    ∃ (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) (r : s.Strictification),
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.transformation) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) := by
  obtain ⟨s, ⟨r⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanRelativeJoinStrictification_exists δ F₀ F α
  exact ⟨s, r, r.transformation_hom_eq⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
