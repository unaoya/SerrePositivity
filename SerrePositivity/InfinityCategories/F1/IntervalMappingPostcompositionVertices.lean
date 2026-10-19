module

public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostcomposition
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingVertices

/-!
概要：区間写像空間の標的の射による作用。
方針：普遍的な区間の族を後合成し、固定端点の写像空間へ curry する。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon §4.6.6、普遍輸送の対象ごとの評価への自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：端点の表示を指定した等号で揃えた区間写像空間の後合成。
方針：普遍的な区間の族を後合成し、端点条件を等号で正規化する。
規約：パラメーターの族そのものは変えない。
使われ方：関手頂点の評価と図式の実際の値の表示を揃える。 -/
noncomputable def intervalMappingPostOfEq {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y') :
    intervalMappingSpace x y ⟶ intervalMappingSpace x' y' :=
  intervalMappingCurryOfEndpoints (intervalMappingUncurry (𝟙 (intervalMappingSpace x y)) ≫ f)
    (by rw [← Category.assoc, intervalMappingUncurry_zero, SSet.const_comp, hx])
    (by rw [← Category.assoc, intervalMappingUncurry_one, SSet.const_comp, hy])

/-- 概要：後合成の普遍的な族は元の普遍的な族の後合成。
方針：既存の任意のパラメーターでの公式に恒等射を入れる。
規約：既存の区間写像空間の後合成をそのまま使う。
使われ方：後合成の頂点と端点の表示変更の計算。 -/
lemma intervalMappingPost_universal_uncurry {X Y : SSet.{u}}
    (f : X ⟶ Y) (x y : X _⦋0⦌) :
    intervalMappingUncurry (intervalMappingPost f x y) =
      intervalMappingUncurry (𝟙 (intervalMappingSpace x y)) ≫ f := by
  simpa only [Category.id_comp] using intervalMappingPost_uncurry f x y (𝟙 _)

/-- 概要：後合成に対応する底の普遍的な区間の族の厳密な計算。
方針：区間の族のパラメーターの前合成と後合成の式を比較する。
規約：追加パラメーターは全区間写像空間。
使われ方：輸送族のパラメーター変更の底の条件。 -/
lemma intervalMappingPost_universal {X Y : SSet.{u}}
    (f : X ⟶ Y) (x y : X _⦋0⦌) :
    (Δ[1] ◁ intervalMappingPost f x y) ≫
        intervalMappingUncurry (𝟙 (intervalMappingSpace (f.app _ x) (f.app _ y))) =
      intervalMappingUncurry (𝟙 (intervalMappingSpace x y)) ≫ f := by
  rw [← intervalMappingUncurry_precomp, Category.comp_id, intervalMappingPost_universal_uncurry]

/-- 概要：区間写像空間の後合成は実際の辺の像を返す。
方針：区間の族を辺の頂点で評価し、Yoneda の自然性を使う。
規約：頂点の等式。
使われ方：パラメーター付き比較の辺での回収。 -/
lemma intervalMappingPost_vertex {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (intervalMappingPost f x y).app _ (intervalMappingVertexOfEdge e) =
      intervalMappingVertexOfEdge (e.map f) := by
  apply Subtype.ext
  apply (functorVertexEquiv (Δ[1] : SSet.{u}) Y).symm.injective
  have h := uncurry_at_vertex
    (intervalMappingPost f x y ≫ vertexFiberι ((pre (boundary 1).ι).app Y)
      (functorVertex (intervalMappingBoundary (f.app _ x) (f.app _ y))))
    (intervalMappingVertexOfEdge e)
  change _ = (functorVertexEquiv (Δ[1] : SSet.{u}) Y).symm
    (((intervalMappingPost f x y).app _ (intervalMappingVertexOfEdge e)).val) at h
  rw [← h]
  change lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (intervalMappingVertexOfEdge e)) ≫
    intervalMappingUncurry (intervalMappingPost f x y) = _
  rw [intervalMappingPost_universal_uncurry, ← Category.assoc,
    intervalMappingUniversal_at_edge, SSet.yonedaEquiv_symm_comp]
  exact ((functorVertexEquiv (Δ[1] : SSet.{u}) Y).symm_apply_apply _).symm

end SerrePositivity.InfinityCategories
