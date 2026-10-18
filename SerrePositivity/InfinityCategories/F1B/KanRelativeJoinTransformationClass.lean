module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCorrectionSquares

/-!
概要：相対 join の厳密化が指定自然変換の h Fun の類を保存することを証明する。
方針：両補正正方形の側辺の類を比較し、可逆な左辺を消去する。
規約：端点同型の代表の選び直しは、raw な等式ではなく Arrow の類の等式で扱う。
使われ方：指定変換を保った相対 join への還元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱比較と厳密化の正方形の左辺は同じ h Fun の射を表す。
方針：両端の同時の比較の類を左端へ制限し、各側辺の raw な表示を使う。
規約：両側辺の代表そのものの一致は要求しない。
使われ方：正方形による上辺の類の比較。 -/
lemma LeftKanRelativeJoinRealization.Strictification.leftBoundary_hom_eq
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (kanPrismHomotopyLeft s.prismTransformation β s.comparisonPrismHomotopy)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (kanPrismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)) := by
  have hc := kanFunctorHomotopy_hom_arrow_of_h_eq
    (kanPrismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)
    (functorHomotopyPrecomp s.endpointsIso.simplicialHomotopy (joinEndpointInl K C))
    r.correctionSquare_left_h
  have hb := kanFunctorHomotopy_hom_arrow_of_h_eq
    (kanPrismHomotopyLeft s.prismTransformation β s.comparisonPrismHomotopy)
    (functorHomotopyPrecomp (functorHomotopyPrecomp s.comparison.simplicialHomotopy
      (kanCylinderEndpointInclusion δ)) (joinEndpointInl K C)) (by
      change _ = (joinEndpointInl K C ▷ (Δ[1] : SSet.{u})) ≫
        (kanCylinderEndpointInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ _
      rw [s.comparisonSquare_left_h, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
      rfl)
  have hm := kanFunctorHomotopy_precomp_hom_arrow _ _ s.endpointsHomotopy_hom_arrow
    (joinEndpointInl K C)
  apply Arrow.mk_injective _ _
  exact hb.trans (hm.symm.trans hc.symm)

/-- 概要：円柱比較と厳密化の正方形の右辺は同じ h Fun の射を表す。
方針：両端の同時の比較の類を右端へ制限し、δ に沿って前合成する。
規約：右辺の始域は K。
使われ方：二つの上辺の類の同定。 -/
lemma LeftKanRelativeJoinRealization.Strictification.rightBoundary_hom_eq
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (kanPrismHomotopyRight s.prismTransformation β s.comparisonPrismHomotopy)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (kanPrismHomotopyRight s.prismTransformation r.transformation
        r.correctionPrismHomotopy)) := by
  have hc := kanFunctorHomotopy_hom_arrow_of_h_eq
    (kanPrismHomotopyRight s.prismTransformation r.transformation r.correctionPrismHomotopy)
    (functorHomotopyPrecomp s.endpointsIso.simplicialHomotopy (δ ≫ joinEndpointInr K C))
    r.correctionSquare_right_h
  have hb := kanFunctorHomotopy_hom_arrow_of_h_eq
    (kanPrismHomotopyRight s.prismTransformation β s.comparisonPrismHomotopy)
    (functorHomotopyPrecomp (functorHomotopyPrecomp s.comparison.simplicialHomotopy
      (kanCylinderEndpointInclusion δ)) (δ ≫ joinEndpointInr K C)) (by
      change _ = ((δ ≫ joinEndpointInr K C) ▷ (Δ[1] : SSet.{u})) ≫
        (kanCylinderEndpointInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ _
      rw [s.comparisonSquare_right_h, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
      rfl)
  have hm := kanFunctorHomotopy_precomp_hom_arrow _ _ s.endpointsHomotopy_hom_arrow
    (δ ≫ joinEndpointInr K C)
  apply Arrow.mk_injective _ _
  exact hb.trans (hm.symm.trans hc.symm)

/-- 概要：厳密化の補正正方形の左辺は可逆。
方針：両端同型の代表の前合成の類は同型の射の前合成である。
規約：別の同型の代表を左辺として選び直さない。
使われ方：h Fun 内で左辺を消去する。 -/
lemma LeftKanRelativeJoinRealization.Strictification.leftBoundary_invertible
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (kanPrismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)) := by
  let H := functorHomotopyPrecomp s.endpointsIso.simplicialHomotopy (joinEndpointInl K C)
  have hi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy H))
    dsimp only [H]
    rw [functorHomotopyPrecomp_hom, kanFunctorIso_simplicialHomotopy_hom]
    infer_instance
  apply (isInvertibleEdge_congr (f := functorEdgeOfSimplicialHomotopy H) ?_).2 hi
  change SSet.yonedaEquiv (curry _) = SSet.yonedaEquiv (curry H.h)
  rw [r.correctionSquare_left_h]
  rfl

/-- 概要：相対 join の端点の厳密化は指定自然変換の h Fun の類を保存する。
方針：共通の下辺を持つ二つの補正正方形で側辺の類を比較し、左の同型を消去する。
規約：δ の単射性は不要。元の β そのものとの raw な等式は主張しない。
使われ方：元の指定変換を保って Kerodon Proposition 7.3.6.1 の相対 join 表示へ移る。 -/
lemma LeftKanRelativeJoinRealization.Strictification.transformation_hom_eq
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r.transformation) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β) :=
  kanFunctorHomSquare_top_hom_eq_of_boundary_classes r.correctionSquare s.comparisonSquare
    r.leftBoundary_hom_eq.symm r.rightBoundary_hom_eq.symm r.leftBoundary_invertible

/-- 概要：端点の厳密化前後で、元の指定変換に関する左 Kan 条件は同値。
方針：指定変換の類の保存を、既存の左 Kan 条件の h 不変性へ渡す。
規約：左 Kan 条件を追加仮定として厳密化データに組み込まない。
使われ方：相対 join 上の図式を用いる大域的普遍性の証明への接続。 -/
lemma LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    IsLeftKanExtension δ F₀ F r.transformation ↔ IsLeftKanExtension δ F₀ F β :=
  isLeftKanExtension_iff_of_homMk_eq δ F₀ F r.transformation β r.transformation_hom_eq

/-- 概要：任意の指定自然変換は、同じ h Fun の類を持つ相対 join の prism で表示できる。
方針：円柱比較の存在、両端の厳密化、変換の類の保存を合成する。
規約：δ の単射性は不要。両端は元の図式に厳密に等しい。
使われ方：Kerodon Proposition 7.3.6.1 の相対 join への還元。 -/
lemma leftKanRelativeJoin_realization_preserving_class {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (β : SSet.Homotopy F₀ (δ ≫ F)) :
    ∃ (s : LeftKanRelativeJoinRealization δ F₀ F β) (r : s.Strictification),
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r.transformation) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β) := by
  obtain ⟨s, ⟨r⟩⟩ := leftKanRelativeJoinStrictification_exists δ F₀ F β
  exact ⟨s, r, r.transformation_hom_eq⟩

end SerrePositivity.InfinityCategories
