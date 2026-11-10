module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TriangleRestriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cocartesian 辺の三角形に沿う合成閉性。
方針：三角形から始点への相対制限を合成し、長辺への制限を消去する。
規約：底を quasicategory とし、射を inner fibration とする。
使われ方：Kerodon Corollary 5.1.2.4、Proposition 5.2.5.1 の transport の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：三角形の最初と後半の辺が cocartesian なら長辺も cocartesian。
方針：最初の辺を経由した始点への充填性を長辺を経由した充填性に移す。
規約：三つの辺はそれぞれ δ₂、δ₀、δ₁ による制限。
使われ方：Kerodon Corollary 5.1.2.4、transport 関手の合成の各頂点での判定。 -/
@[kerodon 01TS]
lemma isCocartesianEdge_triangle_longEdge {X Y : SSet.{u}} [Quasicategory Y]
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (hfirst : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hsecond : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t))) :
    IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t)) := by
  have := relativeCosliceRestriction_triangleFirstEdge t q hsecond
  have := relativeCosliceRestriction_source_of_isCocartesianEdge
    (stdSimplex.δ (2 : Fin 3) ≫ t) q hfirst
  have h := relativeCosliceRestriction_trivialKanFibration_comp t q
    (stdSimplex.δ (2 : Fin 3)) (stdSimplex.δ (1 : Fin 2))
  have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [hv] at h
  have := sliceUnderRestrict_triangleLongEdge (t ≫ q)
  have := relativeCosliceRestriction_triangleLongEdge t q
  have := relativeCosliceRestriction_trivialKanFibration_cancel t q
    (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 2))
  exact isCocartesianEdge_of_relativeCosliceRestriction_source
    (stdSimplex.δ (1 : Fin 3) ≫ t) q

end SerrePositivity.InfinityCategories
