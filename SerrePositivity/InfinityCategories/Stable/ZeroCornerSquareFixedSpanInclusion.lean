module
public import SerrePositivity.InfinityCategories.Stable.SquareFixedSpanCocone

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma zeroCornerSquareFixedSpanRawIso_hom_ι (X : SSet.{u})
    (b : (zeroOuterSpans X) _⦋0⦌) :
    (zeroCornerSquareFixedSpanRawIso X b).hom ≫
      vertexFiberι ((pre spanSquareBoundary).app X) b.val =
    vertexFiberι (zeroCornerSquareSpan X) b ≫
      (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        IsZeroCornerSquareVertex).ι := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (zeroCornerSquareSpanPullbackIso_diagram X) n) v.val

end SerrePositivity.InfinityCategories
