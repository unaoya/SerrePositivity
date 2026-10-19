module
public import SerrePositivity.InfinityCategories.Derived.DGRoofSliceVertices

/-! # 実 over slice の固定図式輸送の台

概要：固定図式の等式輸送は、各単体の join からの射を変えない。
方針：等式を消去し、同じ単体を恒等射で写す式へ戻す。
規約：固定条件の証明には依存しない。使われ方：屋根の頂点と実分母辺の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 固定図式の等式による over slice の輸送は、台の join 射を変えない。 -/
lemma roofSliceTransport_val {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    {d : SimplexCategoryᵒᵖ} (s : (sliceOver p).obj d) :
    ((eqToIso (congrArg sliceOver h)).hom.app d s).val = s.val := by
  subst h
  rfl

/-- 固定図式の輸送は、零単体から回収した実辺の一次単体を変えない。 -/
lemma roofSliceTransport_edge {X : SSet.{u}} {p q : Δ[0] ⟶ X} (h : p = q)
    (s : (sliceOver p) _⦋0⦌) :
    (roofPointSliceVertexEdge q ((eqToIso (congrArg sliceOver h)).hom.app _ s)).edge =
      (roofPointSliceVertexEdge p s).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ _) = _
  rw [roofSliceTransport_val h]
  rfl

/-- 固定点の制限と標的の後合成で変換した slice 頂点の辺を回収する。 -/
lemma roofSlicePostRestrict_edge {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (f : Δ[0] ⟶ K) (s : (sliceOver p) _⦋0⦌) :
    (roofPointSliceVertexEdge (f ≫ (p ≫ q))
      ((sliceOverRestrict (p ≫ q) f).app _ ((sliceOverPostcomp p q).app _ s))).edge =
        q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
          (((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) f) ≫ s.val)) := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    (joinMap (𝟙 Δ[0]) f ≫ (s.val ≫ q))) = _
  simpa only [Category.assoc] using SSet.yonedaEquiv_comp
    (((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) f) ≫ s.val) q

/-- 標的の後合成は、slice 頂点の回収辺の後合成と一致。 -/
lemma roofPointSliceVertexEdge_postcomp {X Y : SSet.{u}} (p : Δ[0] ⟶ X) (q : X ⟶ Y)
    (s : (sliceOver p) _⦋0⦌) :
    (roofPointSliceVertexEdge (p ≫ q) ((sliceOverPostcomp p q).app _ s)).edge =
      q.app (Opposite.op ⦋1⦌) (roofPointSliceVertexEdge p s).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ (s.val ≫ q)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

end SerrePositivity.InfinityCategories
