module
public import SerrePositivity.KST.SConstruction.TriangleUpperEdgeData

/-! # 元の全三角形を指定した実対角辺の合成データとして回収
概要：指定対角辺を持つ元の全二単体から、同じ対角辺を持つ実合成三角形を回収する。
方針：元の全二単体の三辺を取り、対角辺の全区間の等号で端点表示だけを合わせる。
規約：元の全二単体と両元の辺を保持し、三角形を充填し直さない。
使われ方：元の raw 各段の共有対角二面を、型の揃った実 diamond へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の全二単体を、指定した同じ対角辺の実合成表示として保持する。 -/
structure TriangleLongEdgeData {E : SSet.{u}} {x z : E _⦋0⦌}
    (d : E.Edge x z) (t : (Δ[2] : SSet.{u}) ⟶ E) where
  /-- 元の中間頂点。 -/
  middle : E _⦋0⦌
  /-- 元の下面全体を保持する実辺。 -/
  first : E.Edge x middle
  /-- 元の上面全体を保持する実辺。 -/
  second : E.Edge middle z
  /-- 同じ全二単体の実合成三角形。 -/
  triangle : SSet.Edge.CompStruct first second d
  /-- 元の全二単体をそのまま回収する。 -/
  realization_eq : SSet.yonedaEquiv.symm triangle.simplex = t

/-- 指定した実対角辺を持つ同じ全二単体から、両辺を保つ実合成表示を得る。 -/
def triangleLongEdgeData {E : SSet.{u}} {x z : E _⦋0⦌} (d : E.Edge x z)
    (t : (Δ[2] : SSet.{u}) ⟶ E) (hd : stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm d.edge) :
    TriangleLongEdgeData d t := by
  apply Classical.choice
  obtain ⟨v, w, z', a, b, c, T, hT⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv t)
  have ht : SSet.yonedaEquiv.symm T.simplex = t := by rw [hT, Equiv.symm_apply_apply]
  have he : c.edge = d.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 1 ≫ ·) ht)).trans hd)
  have hs : v = x := c.src_eq.symm.trans ((congrArg (E.δ 1) he).trans d.src_eq)
  have hz : z' = z := c.tgt_eq.symm.trans ((congrArg (E.δ 0) he).trans d.tgt_eq)
  exact ⟨⟨w, a.ofEq hs rfl, b.ofEq rfl hz, T.ofEq rfl rfl he, ht⟩⟩

/-- 同じ元の下面の全区間を厳密に回収する。 -/
lemma TriangleLongEdgeData.first_map {E : SSet.{u}} {x z : E _⦋0⦌} {d : E.Edge x z}
    {t : (Δ[2] : SSet.{u}) ⟶ E} (D : TriangleLongEdgeData d t) :
    SSet.yonedaEquiv.symm D.first.edge = stdSimplex.δ 2 ≫ t :=
  (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 2 ≫ ·) D.realization_eq)

/-- 同じ元の上面の全区間も厳密に回収する。 -/
lemma TriangleLongEdgeData.second_map {E : SSet.{u}} {x z : E _⦋0⦌} {d : E.Edge x z}
    {t : (Δ[2] : SSet.{u}) ⟶ E} (D : TriangleLongEdgeData d t) :
    SSet.yonedaEquiv.symm D.second.edge = stdSimplex.δ 0 ≫ t :=
  (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 0 ≫ ·) D.realization_eq)

end SerrePositivity.KST.SConstruction
