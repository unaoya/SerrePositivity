module
public import SerrePositivity.KST.SConstruction.TriangleUpperFaceTransport

/-! # 元の全三角形を指定した実上辺の合成データとして回収
概要：指定上辺を持つ元の全二単体から、同じ上辺を持つ実合成三角形を回収する。
方針：同じ二単体の合成表示を取り、元の上辺全体の等号で端点表示だけを移す。
規約：元の全二単体と両元の辺の像を厳密に保持し、新しい三角形を充填しない。
使われ方：実 BF 段辺と元の直接補正・合成補正を一つの実合成三角形に束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の同じ全二単体を指定実上辺の合成表示として保持するデータ。 -/
structure TriangleUpperEdgeData {E : SSet.{u}} {x y : E _⦋0⦌}
    (b : E.Edge x y) (t : (Δ[2] : SSet.{u}) ⟶ E) where
  /-- 元の三角形の始点。 -/
  source : E _⦋0⦌
  /-- 同じ元の下辺を持つ実辺。 -/
  first : E.Edge source x
  /-- 同じ元の合成辺を持つ実辺。 -/
  direct : E.Edge source y
  /-- 指定上辺と元の二辺を持つ、同じ元の実合成三角形。 -/
  triangle : SSet.Edge.CompStruct first b direct
  /-- 元の全二単体をそのまま保持する。 -/
  realization_eq : SSet.yonedaEquiv.symm triangle.simplex = t

/-- 指定上辺を持つ元の同じ全二単体から、全三辺を持つ実合成データを回収する。 -/
def triangleUpperEdgeData {E : SSet.{u}} {x y : E _⦋0⦌} (b : E.Edge x y)
    (t : (Δ[2] : SSet.{u}) ⟶ E) (hb : stdSimplex.δ 0 ≫ t = SSet.yonedaEquiv.symm b.edge) :
    TriangleUpperEdgeData b t := by
  apply Classical.choice
  obtain ⟨v, w, z, a, c, d, T, hT⟩ := SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv t)
  have ht : SSet.yonedaEquiv.symm T.simplex = t := by rw [hT, Equiv.symm_apply_apply]
  have he : c.edge = b.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 0 ≫ ·) ht)).trans hb)
  have hs : w = x := c.src_eq.symm.trans ((congrArg (E.δ 1) he).trans b.src_eq)
  have hd : z = y := c.tgt_eq.symm.trans ((congrArg (E.δ 0) he).trans b.tgt_eq)
  exact ⟨⟨v, a.ofEq rfl hs, d.ofEq rfl hd, T.ofEq rfl he rfl, ht⟩⟩

/-- 元の下辺全体を、同じ全三角形の同じ面として厳密に回収する。 -/
lemma TriangleUpperEdgeData.first_map {E : SSet.{u}} {x y : E _⦋0⦌} {b : E.Edge x y}
    {t : (Δ[2] : SSet.{u}) ⟶ E} (D : TriangleUpperEdgeData b t) :
    SSet.yonedaEquiv.symm D.first.edge = stdSimplex.δ 2 ≫ t :=
  (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 2 ≫ ·) D.realization_eq)

/-- 元の合成辺全体も、同じ全三角形の同じ面として厳密に回収する。 -/
lemma TriangleUpperEdgeData.direct_map {E : SSet.{u}} {x y : E _⦋0⦌} {b : E.Edge x y}
    {t : (Δ[2] : SSet.{u}) ⟶ E} (D : TriangleUpperEdgeData b t) :
    SSet.yonedaEquiv.symm D.direct.edge = stdSimplex.δ 1 ≫ t :=
  (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 1 ≫ ·) D.realization_eq)

end SerrePositivity.KST.SConstruction
