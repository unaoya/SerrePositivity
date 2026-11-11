module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PullbackVerticalInvertible
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：同じ底の辺の退化三角形上にある比較三角形を、任意の部分底の pullback へ戻す。
方針：底の辺を固定した pullback の普遍性で両面と定値な第二辺を回収する。
規約：部分底の充填性は要求しない。
使われ方：部分底上の元の cocartesian 辺の保存の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 比較の退化三角形の第二辺は、同じ終点での定値射。 -/
lemma comparisonTriangleSecondFace_const :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫ stdSimplex.σ 1 =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

variable {E B : SSet.{u}} (p : E ⟶ B) (a : Over B)
  (β : (Δ[1] : SSet.{u}) ⟶ a.left) (t : (Δ[2] : SSet.{u}) ⟶ E)
  (ht : t ≫ p = stdSimplex.σ 1 ≫ β ≫ a.hom)

/-- 同じ退化した底の辺を持つ三角形を、部分底上の pullback へ持ち上げる。 -/
def pullbackComparisonTriangle : (Δ[2] : SSet.{u}) ⟶ pullback a.hom p :=
  pullback.lift (stdSimplex.σ 1 ≫ β) t (by simpa only [Category.assoc] using ht.symm)

/-- 同じ三角形の第一射影は、元の部分底の辺の退化三角形。 -/
lemma pullbackComparisonTriangle_fst :
    pullbackComparisonTriangle p a β t ht ≫ pullback.fst a.hom p = stdSimplex.σ 1 ≫ β :=
  pullback.lift_fst _ _ _

/-- 同じ三角形の第二射影は、元の全空間の同じ三角形。 -/
lemma pullbackComparisonTriangle_snd :
    pullbackComparisonTriangle p a β t ht ≫ pullback.snd a.hom p = t :=
  pullback.lift_snd _ _ _

/-- 第一辺または長辺の両射影を指定すると、同じ元の辺を厳密に回収する。 -/
lemma pullbackComparisonTriangle_face (j : Fin 3) (hj : j = 1 ∨ j = 2)
    (e : (pullback a.hom p) _⦋1⦌)
    (hb : SSet.yonedaEquiv.symm e ≫ pullback.fst a.hom p = β)
    (he : stdSimplex.δ j ≫ t = SSet.yonedaEquiv.symm e ≫ pullback.snd a.hom p) :
    stdSimplex.δ j ≫ pullbackComparisonTriangle p a β t ht = SSet.yonedaEquiv.symm e := by
  have hs : (stdSimplex.δ j : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫ stdSimplex.σ 1 = 𝟙 _ := by
    rcases hj with rfl | rfl <;> apply SSet.yonedaEquiv.injective <;> decide
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackComparisonTriangle_fst, ← Category.assoc, hs, Category.id_comp]
    exact hb.symm
  · rw [Category.assoc, pullbackComparisonTriangle_snd]
    exact he

/-- 同じ三角形の第二辺は、部分底でも同じ終点上にある。 -/
lemma pullbackComparisonTriangle_vertical :
    (stdSimplex.δ 0 ≫ pullbackComparisonTriangle p a β t ht) ≫ pullback.fst a.hom p =
      SSet.const (β.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  rw [Category.assoc, pullbackComparisonTriangle_fst, ← Category.assoc,
    comparisonTriangleSecondFace_const, SSet.const_comp]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
