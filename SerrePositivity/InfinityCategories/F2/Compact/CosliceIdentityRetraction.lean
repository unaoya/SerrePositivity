module

public import SerrePositivity.InfinityCategories.Stable.CoconeLeg
public import SerrePositivity.InfinityCategories.F1.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.F2.Idempotent.RetractionTriangle

/-!
概要：元の coslice の恒等余錐へ入る実際の辺から、元の二頂点の retract を回収する。
方針：元の legCompStruct の全二単体を同じ包含・射影・恒等辺の三角形として読む。
規約：元の辺と射影を保持し、retract の存在を入力に要求しない。
使われ方：compact 対象の恒等点の因子化から、元の生成項への retract を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の恒等余錐そのものを、元の coslice 射影の同じ頂点上の点として保持する。 -/
def cosliceIdentityFiberPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) x _⦋0⦌ :=
  ⟨cosliceIdentityCone x, (cosliceIdentityCone_projection x).trans
    (pinchedConstant_zero x).symm⟩

/-- 元の coslice の恒等点へ入る辺は、元の同じ二頂点を持つ retract を与える。 -/
lemma cosliceIdentityEdge_retract {X : SSet.{u}} {x y : X _⦋0⦌}
    (w : vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y _⦋0⦌)
    (k : (sliceUnder (SSet.yonedaEquiv.symm x)).Edge w.val (cosliceIdentityCone x)) :
    Idempotent.IsVertexRetractOf x y := by
  let f := cosliceFiberVertexToEdge w
  let g := (k.map (sliceUnderProjection (SSet.yonedaEquiv.symm x))).ofEq
    (w.property.trans (pinchedConstant_zero y)) (cosliceIdentityCone_projection x)
  let t := JoinCocone.legCompStruct (c := w.val) k.toTruncated (𝟙 (Δ[0] : SSet.{u}))
  have h : f.CompStruct g (SSet.Edge.id x) := by
    refine ⟨t.simplex, ?_, t.d₀, ?_⟩
    · rw [t.d₂]
      change SSet.yonedaEquiv (_ ≫ joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ w.val.val) = _
      rw [joinMap_id, Category.id_comp]
      rfl
    · rw [t.d₁]
      change SSet.yonedaEquiv (_ ≫ _ ≫ SSet.const x) = _
      rw [SSet.comp_const, SSet.comp_const]
      exact pinchedConstant_one x
  exact ⟨Idempotent.RetractionTriangle.vertexRetraction ⟨f, g, h⟩⟩

end SerrePositivity.InfinityCategories.F2.Compact
