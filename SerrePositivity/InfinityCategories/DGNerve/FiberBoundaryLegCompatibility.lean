module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryRawComparison
public import SerrePositivity.InfinityCategories.DGNerve.CospanOneTailTransport

/-! # 標準 fiber の境界の脚側整合式

概要：実際の slice 境界の型付き残差は標準射影との微分整合式を満たす。
方針：生の Bianchi を対象・次数・射の異種等号に沿って移す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知先頭成分の微分を計算する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：実際の境界の r_B の微分は射影と r₀ の合成の負に等しい。
方針：零未知データの脚側 Bianchi を標準 fiber の Hom 座標に移す。
規約：HA Proposition 1.3.1.10。使われ方：fiber の線形系の整合条件。 -/
lemma fiberBoundaryRhsB_differential {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    δ (fiberBoundaryDegree n + 1) (fiberBoundaryDegree n + 1 + 1)
        (fiberBoundaryRhsB g h b hb) =
      -(fiberBoundaryRhs0 g h b hb).comp (Cochain.ofHom (pullbackProjectionB g h))
        (add_zero (fiberBoundaryDegree n + 1 + 1)) := by
  have H := SimplexData.cospan_oneTail_differential_of_heq (A := A) (D := Complex A)
    (fiberBoundaryLeftBase g h b)
    (fiberBoundaryLeftBase_equation g h b) (fiberBoundaryLeftBase_prefixHom g h b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    rfl (fiberSliceBoundary_left_apex g h b hb)
    (fiberSliceBoundary_left_B g h b hb) rfl
    (fiberBoundaryRhs0 g h b hb) (fiberBoundaryRhsB g h b hb)
    (Cochain.ofHom (pullbackProjectionB g h))
    (fiberBoundaryRhs0_heq_raw g h b hb).symm
    (fiberBoundaryRhsB_heq_raw g h b hb).symm
    (fiberSliceBoundary_left_projection_heq g h b hb)
  rw [Checks.complex_compose] at H
  exact H

/-- 概要：実際の境界の r_C の微分は射影と r₀ の合成の負に等しい。
方針：零未知データの脚側 Bianchi を標準 fiber の Hom 座標に移す。
規約：HA Proposition 1.3.1.10。使われ方：fiber の線形系の整合条件。 -/
lemma fiberBoundaryRhsC_differential {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    δ (fiberBoundaryDegree n + 1) (fiberBoundaryDegree n + 1 + 1)
        (fiberBoundaryRhsC g h b hb) =
      -(fiberBoundaryRhs0 g h b hb).comp (Cochain.ofHom (pullbackProjectionC g h))
        (add_zero (fiberBoundaryDegree n + 1 + 1)) := by
  have H := SimplexData.cospan_oneTail_differential_of_heq (A := A) (D := Complex A)
    (fiberBoundaryRightBase g h b)
    (fiberBoundaryRightBase_equation g h b) (fiberBoundaryRightBase_prefixHom g h b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_apex g h b hb)
    (fiberSliceBoundary_right_C g h b hb) rfl
    (fiberBoundaryRhs0 g h b hb) (fiberBoundaryRhsC g h b hb)
    (Cochain.ofHom (pullbackProjectionC g h))
    (fiberBoundaryRhs0_heq_right g h b hb).symm
    (fiberBoundaryRhsC_heq_raw g h b hb).symm
    (fiberSliceBoundary_right_projection_heq g h b hb)
  rw [Checks.complex_compose] at H
  exact H

end SerrePositivity.InfinityCategories.DGNerve
