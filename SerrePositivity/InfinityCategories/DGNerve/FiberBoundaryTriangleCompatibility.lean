module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryRawComparison
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailTransport

/-! # 標準 fiber の境界の三角形側整合式

概要：実際の slice 境界の三角形残差は標準射とホモトピーとの微分整合式を満たす。
方針：生の三角形側 Bianchi を共通の Hom 座標へ移す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知六成分の解の微分を検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：実際の境界の r_BD は標準三角形の微分整合式を満たす。
方針：零未知データの三角形 Bianchi を標準 Hom 座標へ移し、線形性で整理する。
規約：HA Proposition 1.3.1.10。使われ方：fiber の線形系の三角形側整合条件。 -/
lemma fiberBoundaryRhsBD_differential {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    δ (fiberBoundaryDegree n) (fiberBoundaryDegree n + 1)
        (fiberBoundaryRhsBD g h b hb) =
      fiberBoundaryRhsD g h b hb -
        (fiberBoundaryRhsB g h b hb).comp (Cochain.ofHom g)
          (add_zero (fiberBoundaryDegree n + 1)) -
        (fiberBoundaryRhs0 g h b hb).comp (fiberNullHomotopy (fiberDifference g h))
          (by omega) := by
  have H := SimplexData.cospan_twoTail_differential_of_heq (A := A) (D := Complex A)
    (fiberBoundaryLeftBase g h b)
    (fiberBoundaryLeftBase_equation g h b) (fiberBoundaryLeftBase_unknownHom g h b)
    rfl (fiberSliceBoundary_left_apex g h b hb)
    (fiberSliceBoundary_left_B g h b hb) (fiberSliceBoundary_left_D g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    (fiberBoundaryRhs0 g h b hb) (fiberBoundaryRhsB g h b hb)
    (fiberBoundaryRhsD g h b hb) (fiberBoundaryRhsBD g h b hb)
    (Cochain.ofHom g) (fiberNullHomotopy (fiberDifference g h))
    (fiberBoundaryRhs0_heq_raw g h b hb).symm
    (fiberBoundaryRhsB_heq_raw g h b hb).symm
    (((fiberBoundaryLeftBase g h b).cospanTwoTailLastRhs_heq).trans
      (fiberBoundaryRhsD_heq_raw g h b hb).symm)
    (fiberBoundaryRhsBD_heq_raw g h b hb).symm
    (fiberSliceBoundary_left_cospan_heq g h b hb)
    (fiberSliceBoundary_left_homotopy_heq g h b hb)
  change δ _ _ (fiberBoundaryRhsBD g h b hb) = _ at H
  simp only [Checks.complex_compose] at H
  rw [H]
  abel

/-- 概要：実際の境界の r_CD は標準三角形の微分整合式を満たす。
方針：零未知データの三角形 Bianchi を標準 Hom 座標へ移し、線形性で整理する。
規約：HA Proposition 1.3.1.10。使われ方：fiber の線形系の三角形側整合条件。 -/
lemma fiberBoundaryRhsCD_differential {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    δ (fiberBoundaryDegree n) (fiberBoundaryDegree n + 1)
        (fiberBoundaryRhsCD g h b hb) =
      fiberBoundaryRhsD g h b hb -
        (fiberBoundaryRhsC g h b hb).comp (Cochain.ofHom h)
          (add_zero (fiberBoundaryDegree n + 1)) := by
  have H := SimplexData.cospan_twoTail_differential_of_heq (A := A) (D := Complex A)
    (fiberBoundaryRightBase g h b)
    (fiberBoundaryRightBase_equation g h b) (fiberBoundaryRightBase_unknownHom g h b)
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_apex g h b hb)
    (fiberSliceBoundary_right_C g h b hb) (fiberSliceBoundary_right_D g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    (fiberBoundaryRhs0 g h b hb) (fiberBoundaryRhsC g h b hb)
    (fiberBoundaryRhsD g h b hb) (fiberBoundaryRhsCD g h b hb)
    (Cochain.ofHom h) (0 : Cochain (pullbackFiber g h) D (-1))
    (fiberBoundaryRhs0_heq_right g h b hb).symm
    (fiberBoundaryRhsC_heq_raw g h b hb).symm
    (((fiberBoundaryRightBase g h b).cospanTwoTailLastRhs_heq).trans
      (fiberBoundaryRhsD_heq_right g h b hb).symm)
    (fiberBoundaryRhsCD_heq_raw g h b hb).symm
    (fiberSliceBoundary_right_cospan_heq g h b hb)
    (fiberSliceBoundary_right_homotopy_heq g h b hb)
  change δ _ _ (fiberBoundaryRhsCD g h b hb) = _ at H
  simp only [Checks.complex_compose, Cochain.comp_zero] at H
  rw [H]
  abel

end SerrePositivity.InfinityCategories.DGNerve
