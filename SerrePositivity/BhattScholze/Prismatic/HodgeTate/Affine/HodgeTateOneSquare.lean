module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateBocksteinSquare
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateBocksteinSquare
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneGenerators
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing

/-!
# 一次 Hodge–Tate 写像の平方零

## 概要
完備一次形式の像はすべて cup 平方が零。

## 方針
各座標の像は Bockstein なので平方が零。係数は零次にあり、異なる一次の交差項は相殺する。

## 規約
素数 2 にも同じ加法と係数の議論を使う。

## 使われ方
外積代数の普遍性。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
open scoped DirectSum TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

local notation "X" => reducedModel P hP r
local notation "H" => hodgeTateCohomology' P hP r
local notation "R" => affineAlgebra P r
local notation "k" => A ⧸ P.ideal
local notation "T" => oneVars A r
local notation "Q" => completedPoly k T p

local instance htSquareAffineModule (i : ℕ) : Module R (H i) := htModule P hP r i
local instance htSquareGradedRing : DirectSum.GRing (H) := cohomologyCupGradedRing X

private theorem htCup_sq_add (a b : H 1) (ha : cohomologyCup X a a = 0)
    (hb : cohomologyCup X b b = 0) : cohomologyCup X (a+b) (a+b) = 0 := by
  have h := cohomologyCup_comm X a b
  have hab : cohomologyCup X a b = - cohomologyCup X b a := by
    simpa only [cast_eq, Nat.mul_one, pow_one, neg_one_zsmul] using h
  rw [cohomologyCup_add_left, cohomologyCup_add_right, cohomologyCup_add_right, ha, hb, hab]
  abel

private theorem htCup_sq_smul (f : R) (z : H 1) (hz : cohomologyCup X z z = 0) :
    cohomologyCup X (f • z) (f • z) = 0 := by
  let J := DirectSum.of (H)
  let a := hodgeTateMapZero P hP r f
  have h₀ : J 0 a * J 1 z = J 1 (f • z) := by
    rw [DirectSum.of_mul_of]
    have h := (htModuleData P hP r 1).property f z
    change f • z = cohomologyCup X a z at h
    rw [h]
    rfl
  have hcomm : Commute (J 1 z) (J 0 a) := by
    show J 1 z * J 0 a = J 0 a * J 1 z
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    have h := cup_one_zero_comm X z a
    change J 1 (cohomologyCup X z a) = J 1 (cohomologyCup X a z)
    rw [h]
  have h₁ : J 1 z * J 1 z = 0 := by
    rw [DirectSum.of_mul_of]
    change J 2 (cohomologyCup X z z) = 0
    rw [hz, map_zero]
  have h : J 1 (f • z) * J 1 (f • z) = 0 := by
    rw [← h₀, ← mul_assoc, mul_assoc (J 0 a) (J 1 z), hcomm.eq, ← mul_assoc (J 0 a),
      mul_assoc, h₁, mul_zero]
  rw [DirectSum.of_mul_of] at h
  apply DirectSum.of_injective (β := H) 2
  change J 2 (cohomologyCup X (f • z) (f • z)) = J 2 0
  rw [map_zero]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- 一次の Hodge–Tate 像は外積の平方零条件を満たす。 -/
theorem hodgeTateMapOne_square_zero (ω : affineForms P r 1) :
    cohomologyCup X (hodgeTateMapOne P hP r ω) (hodgeTateMapOne P hP r ω) = 0 := by
  let : Module Q (H 1) := Module.compHom _ (affineCoordinateIso P r).symm.toRingHom
  let b := htOneBasis P r
  let E := htOneBaseChange P r
  let F := htOneCoefficientMap P hP r
  let c := b.repr (E ω)
  have h := b.sum_repr (E ω)
  have hω : hodgeTateMapOne P hP r ω =
      ∑ t : T, (affineCoordinateIso P r).symm (c t) •
        bockstein P hP r 0 (hodgeTateMapZero P hP r
          (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down))) := by
    change F (E ω) = _
    rw [← h, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_smul]
    dsimp only [F, b]
    rw [htOneCoefficientMap, Module.Basis.constr_basis]
    rfl
  rw [hω]
  apply Finset.sum_induction _ (fun z : H 1 => cohomologyCup X z z = 0)
  · intro a b
    exact htCup_sq_add P hP r a b
  · exact (cohomologyCupGradedRing X).zero_mul (i := 1) (0 : H 1)
  · intro t _
    apply htCup_sq_smul P hP r
    exact bockstein_sq_zero P hP r _

end SerrePositivity.BhattScholze.Prismatic
