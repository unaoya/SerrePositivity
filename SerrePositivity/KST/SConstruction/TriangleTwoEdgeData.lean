module
public import SerrePositivity.KST.SConstruction.TriangleLongEdgeData

/-! # 指定した二辺を持つ元の全三角形の型を揃える
概要：元の全二単体を保持し、指定済み二辺と同じ端点を持つ残る実辺を回収する。
方針：同じ全二単体の合成表示と全辺の等号から端点の表示だけを移す。
規約：同じ元の全三角形を保持し、新しい面・辺を充填しない。
使われ方：元の raw 十二面を型の揃った六つの実 diamond へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 指定した下面・上面と、元の全二単体を保持する合成表示。 -/
structure TrianglePairEdgeData {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) (t : (Δ[2] : SSet.{u}) ⟶ E) where
  /-- 元の全対角辺。 -/
  direct : E.Edge x z
  /-- 指定した両辺を持つ元の同じ全三角形。 -/
  triangle : SSet.Edge.CompStruct a b direct
  /-- 元の全二単体をそのまま保持する。 -/
  realization_eq : SSet.yonedaEquiv.symm triangle.simplex = t

/-- 下面・上面を指定した元の全二単体から、同じ全合成表示を回収する。 -/
def trianglePairEdgeData {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) (t : (Δ[2] : SSet.{u}) ⟶ E)
    (ha : stdSimplex.δ 2 ≫ t = SSet.yonedaEquiv.symm a.edge)
    (hb : stdSimplex.δ 0 ≫ t = SSet.yonedaEquiv.symm b.edge) : TrianglePairEdgeData a b t := by
  apply Classical.choice
  obtain ⟨v, w, z', a', b', c, T, hT⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv t)
  have ht : SSet.yonedaEquiv.symm T.simplex = t := by rw [hT, Equiv.symm_apply_apply]
  have he : a'.edge = a.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 2 ≫ ·) ht)).trans ha)
  have hf : b'.edge = b.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 0 ≫ ·) ht)).trans hb)
  have hs : v = x := a'.src_eq.symm.trans ((congrArg (E.δ 1) he).trans a.src_eq)
  have hz : z' = z := b'.tgt_eq.symm.trans ((congrArg (E.δ 0) hf).trans b.tgt_eq)
  exact ⟨⟨c.ofEq hs hz, T.ofEq he hf rfl, ht⟩⟩

/-- 指定した下面・対角面と、元の全二単体を保持する合成表示。 -/
structure TriangleLowerDirectData {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (d : E.Edge x z) (t : (Δ[2] : SSet.{u}) ⟶ E) where
  /-- 元の全上辺。 -/
  second : E.Edge y z
  /-- 指定した両辺を持つ元の同じ全三角形。 -/
  triangle : SSet.Edge.CompStruct a second d
  /-- 元の全二単体をそのまま保持する。 -/
  realization_eq : SSet.yonedaEquiv.symm triangle.simplex = t

/-- 下面・対角面を指定した元の全二単体から、同じ全合成表示を回収する。 -/
def triangleLowerDirectData {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (d : E.Edge x z) (t : (Δ[2] : SSet.{u}) ⟶ E)
    (ha : stdSimplex.δ 2 ≫ t = SSet.yonedaEquiv.symm a.edge)
    (hd : stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm d.edge) : TriangleLowerDirectData a d t := by
  apply Classical.choice
  obtain ⟨v, w, z', a', b', c, T, hT⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv t)
  have ht : SSet.yonedaEquiv.symm T.simplex = t := by rw [hT, Equiv.symm_apply_apply]
  have he : a'.edge = a.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 2 ≫ ·) ht)).trans ha)
  have hf : c.edge = d.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 1 ≫ ·) ht)).trans hd)
  have hm : w = y := a'.tgt_eq.symm.trans ((congrArg (E.δ 0) he).trans a.tgt_eq)
  have hz : z' = z := c.tgt_eq.symm.trans ((congrArg (E.δ 0) hf).trans d.tgt_eq)
  exact ⟨⟨b'.ofEq hm hz, T.ofEq he rfl hf, ht⟩⟩

/-- 指定した上面・対角面と、元の全二単体を保持する合成表示。 -/
structure TriangleUpperDirectData {E : SSet.{u}} {x y z : E _⦋0⦌}
    (b : E.Edge y z) (d : E.Edge x z) (t : (Δ[2] : SSet.{u}) ⟶ E) where
  /-- 元の全下辺。 -/
  first : E.Edge x y
  /-- 指定した両辺を持つ元の同じ全三角形。 -/
  triangle : SSet.Edge.CompStruct first b d
  /-- 元の全二単体をそのまま保持する。 -/
  realization_eq : SSet.yonedaEquiv.symm triangle.simplex = t

/-- 上面・対角面を指定した元の全二単体から、同じ全合成表示を回収する。 -/
def triangleUpperDirectData {E : SSet.{u}} {x y z : E _⦋0⦌}
    (b : E.Edge y z) (d : E.Edge x z) (t : (Δ[2] : SSet.{u}) ⟶ E)
    (hb : stdSimplex.δ 0 ≫ t = SSet.yonedaEquiv.symm b.edge)
    (hd : stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm d.edge) : TriangleUpperDirectData b d t := by
  apply Classical.choice
  obtain ⟨v, w, z', a', b', c, T, hT⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv t)
  have ht : SSet.yonedaEquiv.symm T.simplex = t := by rw [hT, Equiv.symm_apply_apply]
  have he : b'.edge = b.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 0 ≫ ·) ht)).trans hb)
  have hf : c.edge = d.edge := SSet.yonedaEquiv.symm.injective
    (((SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm T).symm.trans
      (congrArg (stdSimplex.δ 1 ≫ ·) ht)).trans hd)
  have hs : v = x := c.src_eq.symm.trans ((congrArg (E.δ 1) hf).trans d.src_eq)
  have hm : w = y := b'.src_eq.symm.trans ((congrArg (E.δ 1) he).trans b.src_eq)
  exact ⟨⟨a'.ofEq hs hm, T.ofEq rfl he hf, ht⟩⟩

/-- 指定した両辺の元の対角辺全体を厳密に回収する。 -/
lemma TrianglePairEdgeData.direct_map {E : SSet.{u}} {x y z : E _⦋0⦌}
    {a : E.Edge x y} {b : E.Edge y z} {t : (Δ[2] : SSet.{u}) ⟶ E}
    (D : TrianglePairEdgeData a b t) :
    SSet.yonedaEquiv.symm D.direct.edge = stdSimplex.δ 1 ≫ t :=
  (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 1 ≫ ·) D.realization_eq)

/-- 下面・対角面を指定した元の上辺全体を厳密に回収する。 -/
lemma TriangleLowerDirectData.second_map {E : SSet.{u}} {x y z : E _⦋0⦌}
    {a : E.Edge x y} {d : E.Edge x z} {t : (Δ[2] : SSet.{u}) ⟶ E}
    (D : TriangleLowerDirectData a d t) :
    SSet.yonedaEquiv.symm D.second.edge = stdSimplex.δ 0 ≫ t :=
  (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 0 ≫ ·) D.realization_eq)

/-- 上面・対角面を指定した元の下辺全体を厳密に回収する。 -/
lemma TriangleUpperDirectData.first_map {E : SSet.{u}} {x y z : E _⦋0⦌}
    {b : E.Edge y z} {d : E.Edge x z} {t : (Δ[2] : SSet.{u}) ⟶ E}
    (D : TriangleUpperDirectData b d t) :
    SSet.yonedaEquiv.symm D.first.edge = stdSimplex.δ 2 ≫ t :=
  (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm D.triangle).symm.trans
    (congrArg (stdSimplex.δ 2 ≫ ·) D.realization_eq)

end SerrePositivity.KST.SConstruction
