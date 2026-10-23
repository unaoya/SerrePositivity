module

public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：任意の部分底上の射は、同じ頂点 fiber 内で可逆な辺を可逆な辺へ送る。
方針：元の quasicategory の固定 fiber に辺を戻し、その fiber からの射として像を計算する。
規約：部分底とその上の全空間の quasicategory 性を要求しない。
使われ方：部分底上の cocartesian 比較三角形の第二辺の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 任意の部分底で、元の fiber 内の可逆辺は同じ部分空間からの射でも可逆に写る。 -/
lemma isInvertibleEdge_partialPullback_map_of_vertical
    {E F B : SSet.{u}} [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (a : Over B) (H : pullback a.hom p ⟶ F)
    (e : (pullback a.hom p) _⦋1⦌) (v : a.left _⦋0⦌)
    (hbase : SSet.yonedaEquiv.symm e ≫ pullback.fst a.hom p = SSet.const v)
    (he : IsInvertibleEdge (edgeOfSimplex ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e))) :
    IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌) e)) := by
  let b := a.hom.app (Opposite.op ⦋0⦌) v
  let u := SSet.yonedaEquiv.symm e ≫ pullback.snd a.hom p
  have hu : u ≫ p = SSet.const b := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hbase, SSet.const_comp]
  let L := vertexFiberLift p b u hu
  let J : vertexFiber p b ⟶ pullback a.hom p :=
    pullback.lift (SSet.const v) (vertexFiberι p b) (by
      rw [SSet.const_comp, vertexFiberι_comp])
  have hL : L ≫ vertexFiberι p b = u := vertexFiberLift_ι _ _ _ _
  have hi : (vertexFiberι p b).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) =
      (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e := by
    rw [← SSet.yonedaEquiv_comp, hL, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hLF : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv L)) := by
    apply (isInvertibleEdge_vertexFiber_iff p b _).mpr
    exact (isInvertibleEdge_congr hi).mpr he
  have hLJ : L ≫ J = SSet.yonedaEquiv.symm e := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, SSet.comp_const]
      exact hbase.symm
    · rw [Category.assoc, pullback.lift_snd]
      exact hL
  have hm := hLF.map (J ≫ H)
  have ho : (J ≫ H).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) =
      H.app (Opposite.op ⦋1⦌) e := by
    rw [← SSet.yonedaEquiv_comp, ← Category.assoc, hLJ,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (isInvertibleEdge_congr ho).mp hm

end SerrePositivity.InfinityCategories
