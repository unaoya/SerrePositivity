module
public import SerrePositivity.InfinityCategories.Stable.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Stable.ColimitHomotopyUniqueness
public import SerrePositivity.InfinityCategories.Stable.SpanComparisonUniqueness

/-! # 始点固定の cofiber 比較の一意性

概要：押し出し四角形から指定 suspension への始点固定の比較は h で一意である。
方針：span 比較の一意性を、普遍余錐の射影の忠実性で四角形に持ち上げる。
規約：指定した suspension 四角形を固定する。
使われ方：S4 の接続射の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：四角形の始点固定条件は span に制限したホモトピーにも成り立つ。
方針：span の第一辺と四角形の下辺の一致を使う。
規約：値域への追加仮定は不要。使われ方：span 比較の一意性の適用。 -/
lemma stableHomotopyPrecomp_span_source {X : SSet.{u}}
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (H : SSet.Homotopy F G)
    (hH : ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0)) :
    ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫
      (stableHomotopyPrecomp spanSquareBoundary H).h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0) := by
  change ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫
    ((spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ H.h) = _
  rw [← Category.assoc, ← comp_whiskerRight, Category.assoc, spanSquareBoundary_bottomEdge]
  exact hH

/-- 概要：余錐表示へ制限した四角形の比較をさらに図式へ制限すると span の比較の類になる。
方針：二つの前合成を合成し、span の包含の定義を用いる。
規約：quasicategory 性は不要。使われ方：普遍余錐の忠実性への入力。 -/
lemma cofiberComparison_coconeRestriction {X : SSet.{u}}
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (H : SSet.Homotopy F G) :
    (hoFunctor.map (coconeRestriction (horn 2 0 : SSet.{u}) X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp spanCoconeSquareIso.hom H))) =
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp spanSquareBoundary H)) := by
  change (hoFunctor.map ((pre (joinInl (horn 2 0 : SSet.{u}) Δ[0])).app X)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp spanCoconeSquareIso.hom H))) = _
  rw [homMk_functorEdge_precomp]
  congr 1

/-- 概要：始点を固定した指定 suspension への二つの四角形の比較は h で一致する。
方針：span の一意性を普遍余錐の忠実性で持ち上げ、形状の同型を逆に戻す。
規約：元の四角形は押し出し、値域は quasicategory。
使われ方：接続射の比較ホモトピーの選択独立性。 -/
lemma cofiberSuspensionComparison_homMk_eq {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : IsPushoutSquare F)
    (s : SuspensionSquare (squareVertex F 0 0)) (H J : SSet.Homotopy F s.square)
    (hH : ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0))
    (hJ : ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ J.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  have hb := suspensionSpanHomotopy_homMk_eq F s
    (stableHomotopyPrecomp spanSquareBoundary H) (stableHomotopyPrecomp spanSquareBoundary J)
    (stableHomotopyPrecomp_span_source H hH) (stableHomotopyPrecomp_span_source J hJ)
  have hc := colimitCoconeHomotopy_homMk_eq (pushoutCocone F) (pushoutCocone s.square)
    hF s.isPushout (stableHomotopyPrecomp spanCoconeSquareIso.hom H)
      (stableHomotopyPrecomp spanCoconeSquareIso.hom J)
      ((cofiberComparison_coconeRestriction H).trans
        (hb.trans (cofiberComparison_coconeRestriction J).symm))
  have he := congrArg (fun f ↦
    (hoFunctor.map ((pre spanCoconeSquareIso.inv).app X)).toFunctor.map f) hc
  rw [homMk_functorEdge_precomp, homMk_functorEdge_precomp] at he
  apply Arrow.mk_injective
  exact (homMk_functorEdge_precomp_inv_hom_arrow spanCoconeSquareIso H).symm.trans
    ((congrArg Arrow.mk he).trans
      (homMk_functorEdge_precomp_inv_hom_arrow spanCoconeSquareIso J))

end SerrePositivity.InfinityCategories
