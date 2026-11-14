module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.BocksteinCupSquare
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# affine Hodge–Tate の Bockstein 平方零

## 概要
零次からの Bockstein の像は cup 平方が零。

## 方針
p = 2 では δ による余境界を使う。奇素数では p 完備係数環で 2 が単元なので、
cup 積の次数付き可換性で得る等式から 2 を消去する。

## 規約
向きで Bockstein の捻りを自明化する。

## 使われ方
Hodge–Tate 写像の外積への延長。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

private theorem affine_two_isUnit (hp : p ≠ 2) : IsUnit (2 : affineAlgebra P r) := by
  let B := MvPolynomial (Fin r) (A ⧸ P.ideal)
  let R : Type u := affineAlgebra P r
  let : Algebra B R := principalCompletionAlgebra B (p : B)
  have hc : IsModuleComplete R (p : R) (ModuleCat.of R R) := by
    have hh := (isModuleComplete_algebraMap_iff B R (p : B) R).mpr
      (principalCompletionH0_isModuleComplete B (p : B))
    rwa [map_natCast] at hh
  have hu : IsUnit (1 + (p : R)) := by
    convert isUnit_one_sub_mul_of_isModuleComplete R (p : R) hc (-1) using 1
    ring
  obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hf : (1 : R) + (p : R) = 2 * ((a : R) + 1) := by
    have he := congrArg (fun n : ℕ => (n : R)) ha
    rw [he, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
    ring
  rw [hf] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- 零次からの Bockstein 像の平方零。 -/
def BetaSquareZero : Prop := ∀ f : affineAlgebra P r,
  let x := bockstein P hP r 0 (hodgeTateMapZero P hP r f)
  cohomologyCup (reducedModel P hP r) x x = 0

/-- affine 模型の Bockstein 像は外積の平方零条件を満たす。 -/
theorem bockstein_sq_zero : BetaSquareZero P hP r := by
  intro f
  by_cases hp : p = 2
  · subst p
    exact cupBockstein_cup_sq_two (htRings P hP r)
      (fun n => ((htCech P hP r).obj n).Q.deltaStructure)
      (fun θ => ((htCech P hP r).map θ).toHom.map_delta)
      (htGenerator P hP r) (htGenerator_nat P hP r) (htGenerator_regular P hP r)
      A (htBase P hP r) (hodgeTateMapZero P hP r f)
  · let x := bockstein P hP r 0 (hodgeTateMapZero P hP r f)
    let y := cohomologyCup (reducedModel P hP r) x x
    have h : y = -y := by
      simpa only [cast_eq, Nat.zero_add, Nat.mul_one, pow_one, neg_one_zsmul] using
        cohomologyCup_comm (reducedModel P hP r) x x
    let := htModule P hP r 2
    apply (affine_two_isUnit P r hp).smul_eq_zero.mp
    change (2 : affineAlgebra P r) • y = 0
    rw [two_smul]
    exact (congrArg (fun t => t + y) h).trans (neg_add_cancel y)

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 4.10" (partial := special) "任意の有界向き付き基底の上の多項式代数で証明済み（BS-D68）。原典は Prop 6.2 から導くが、本体は直接の証明（p=2 では δ による余境界、奇素数では cup 積の次数付き可換性） ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.bockstein_sq_zero
