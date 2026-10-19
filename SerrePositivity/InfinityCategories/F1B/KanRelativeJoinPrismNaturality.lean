module

public import SerrePositivity.InfinityCategories.F1B.KanPrecompositionHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCoconeTransport
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinBaseFiber

/-!
概要：相対 join の標準 prism が与える変換の大域的な自然性。
方針：prism を内部 Hom の前合成作用へ写し、その自然変換の自然性を評価する。
規約：射は h Fun の任意の射で、可逆性を要求しない。
使われ方：右端の対応の単位と標準 Kan 変換の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の prism の変換は図式間の任意の二胞体に自然。
方針：恒等図式の prism の前合成作用を評価し、自然性の正方形を取り出す。
規約：quasicategory 性を要求しない。
使われ方：右端で恒等となる大域的な単位の左端での計算。 -/
lemma kanRelativeJoinTransformation_naturality {K C D : SSet.{u}}
    (p : K ⟶ C) {H G : relativeJoin p (𝟙 C) ⟶ D} (α : FunctorHom H G) :
    (hoFunctor.map ((pre (relativeJoinInl p (𝟙 C))).app D)).toFunctor.map α ≫
        SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy (kanRelativeJoinTransformation p G)) =
      SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy (kanRelativeJoinTransformation p H)) ≫
        (hoFunctor.map ((pre (p ≫ relativeJoinInr p (𝟙 C))).app D)).toFunctor.map α := by
  let T := kanRelativeJoinTransformation p (𝟙 (relativeJoin p (𝟙 C)))
  have h := (kanPrecompositionNatTrans T D).naturality α
  rw [kanPrecompositionNatTrans_app, kanPrecompositionNatTrans_app] at h
  exact h

/-- 概要：底射影に沿う図式の prism の類は端点を同定する恒等射。
方針：prism の底射影を計算し、時間に定値なホモトピーの類の公式を使う。
規約：左右の端点の表示の違いは eqToHom で保持する。
使われ方：標準 prism の自然性の正方形の右辺の消去。 -/
lemma kanRelativeJoinTransformation_base_hom {K C D : SSet.{u}}
    (p : K ⟶ C) (G : C ⟶ D) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (kanRelativeJoinTransformation p (relativeJoinBaseProjection p (𝟙 C) ≫ G))) =
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
        (show relativeJoinInl p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G) =
            p ≫ relativeJoinInr p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G) by
          rw [reassoc_of% (kanRelativeJoinInl_baseProjection p (𝟙 C)),
            reassoc_of% (relativeJoinInr_baseProjection p (𝟙 C))])) := by
  refine kanHomotopyHom_eqToHom _ (by
    rw [reassoc_of% (kanRelativeJoinInl_baseProjection p (𝟙 C)),
      reassoc_of% (relativeJoinInr_baseProjection p (𝟙 C))]) ?_
  change (β_ K (Δ[1] : SSet.{u})).hom ≫ relativeJoinPrism p ≫
      relativeJoinBaseProjection p (𝟙 C) ≫ G =
    fst K (Δ[1] : SSet.{u}) ≫ relativeJoinInl p (𝟙 C) ≫
      relativeJoinBaseProjection p (𝟙 C) ≫ G
  rw [reassoc_of% (relativeJoinPrism_baseProjection p),
    reassoc_of% (kanRelativeJoinInl_baseProjection p (𝟙 C))]
  rfl

end SerrePositivity.InfinityCategories.F1B
