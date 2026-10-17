module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryLegCompatibility
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryTriangleCompatibility
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryUnknowns

/-! # 実際の標準 fiber 境界に対する明示解の微分

概要：実際の境界から作った先頭成分と D 側成分はそれぞれの微分方程式を満たす。
方針：実際の残差整合式を逆 Hom-fiber 座標の微分公式へ代入する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：slice の境界充填の未知成分の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：実際の境界から作った未知先頭成分の微分は先頭右辺に等しい。
方針：脚側と三角形側の実際の整合式を、逆座標の微分公式へ渡す。
規約：HA Proposition 1.3.1.10。使われ方：未知成分 a の方程式 δa=r₀。 -/
lemma fiberBoundaryUnknownA_differential {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    δ (fiberBoundaryDegree n + 1) (fiberBoundaryDegree n + 1 + 1)
      (fiberBoundaryUnknownA g h b hb) = fiberBoundaryRhs0 g h b hb := by
  unfold fiberBoundaryUnknownA
  exact pullbackHomBoundaryLift_differential_of_residuals g h (fiberBoundaryDegree n)
    (fiberBoundaryRhs0 g h b hb) (fiberBoundaryRhsB g h b hb)
    (fiberBoundaryRhsC g h b hb) (fiberBoundaryRhsD g h b hb)
    (fiberBoundaryRhsBD g h b hb) (fiberBoundaryRhsCD g h b hb)
    (fiberBoundaryRhsB_differential g h b hb) (fiberBoundaryRhsC_differential g h b hb)
    (fiberBoundaryRhsBD_differential g h b hb) (fiberBoundaryRhsCD_differential g h b hb)

/-- 概要：実際の境界から作った未知 D 成分の微分は対角射と先頭成分の合成に右辺を加えたもの。
方針：右三角形の整合式と先頭成分の対角座標を使う。
規約：HA Proposition 1.3.1.10。使われ方：未知成分 d の方程式。 -/
lemma fiberBoundaryUnknownD_differential {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    δ (fiberBoundaryDegree n) (fiberBoundaryDegree n + 1) (fiberBoundaryUnknownD g h b hb) =
      (fiberBoundaryUnknownA g h b hb).comp (Cochain.ofHom (pullbackDiagonal g h))
        (add_zero (fiberBoundaryDegree n + 1)) + fiberBoundaryRhsD g h b hb := by
  unfold fiberBoundaryUnknownA fiberBoundaryUnknownD
  exact pullbackBoundary_D_equation g h (fiberBoundaryDegree n)
    (fiberBoundaryRhsB g h b hb) (fiberBoundaryRhsC g h b hb)
    (fiberBoundaryRhsD g h b hb) (fiberBoundaryRhsBD g h b hb) (fiberBoundaryRhsCD g h b hb)
    (fiberBoundaryRhsCD_differential g h b hb)

end SerrePositivity.InfinityCategories.DGNerve
