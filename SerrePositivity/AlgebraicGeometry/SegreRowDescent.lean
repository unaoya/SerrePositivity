module

public import SerrePositivity.AlgebraicGeometry.SegreColumnDescent
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：Segre 座標の行への代入と、因子からの降下。
方針：テンソル積の交換同型で列の評価を使い、斉次な核から全関係式へ移す。
規約：平坦性を仮定しない。
使われ方：二因子のチャートから Segre 標準開への逆写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B) (i : ι)

/-- 行への斉次評価は、テンソル積の交換同型を通じた列への評価。 -/
theorem segreCoordinateMap_row {d : ℕ} (p : MvPolynomial κ R) (hp : p.IsHomogeneous d) :
    segreCoordinateMap (R := R) a b (MvPolynomial.rename (fun l ↦ (i, l)) p) =
      MvPolynomial.aeval (R := R) b p ⊗ₜ[R] ((a i) ^ d) := by
  have hcomp : (segreCoordinateMap (R := R) a b).comp
      (MvPolynomial.rename (fun l ↦ (i, l))) =
      (Algebra.TensorProduct.comm R A B).toAlgHom.comp
        ((segreCoordinateMap (R := R) b a).comp (MvPolynomial.rename (fun l ↦ (l, i)))) := by
    ext l
    simp
  change ((segreCoordinateMap (R := R) a b).comp
    (MvPolynomial.rename (fun l ↦ (i, l)))) p = _
  rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, segreCoordinateMap_column b a i p hp]
  simp

/-- 元の斉次関係式は、Segre 座標の行への代入でも消える。 -/
theorem segreCoordinateProjection_row_zero {d : ℕ} (p : MvPolynomial κ R)
    (hp : p.IsHomogeneous d) (hz : MvPolynomial.aeval (R := R) b p = 0) :
    segreCoordinateProjection (R := R) a b (MvPolynomial.rename (fun l ↦ (i, l)) p) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change segreCoordinateMap (R := R) a b (MvPolynomial.rename (fun l ↦ (i, l)) p) = 0
  rw [segreCoordinateMap_row a b i p hp, hz, TensorProduct.zero_tmul]

/-- 一行への代入を同じ商へ送る実際の多項式代数写像。 -/
def segreRowPolynomialMap : MvPolynomial κ R →ₐ[R] SegreCoordinateRing (R := R) a b :=
  (segreCoordinateProjection (R := R) a b).comp (MvPolynomial.rename (fun l ↦ (i, l)))

variable (H : ℕ → Submodule R B) [GradedRing H] (hb : ∀ l, b l ∈ H 1)
attribute [local instance] MvPolynomial.gradedAlgebra
include H hb

/-- 次数一表示の全関係式は、行の評価で消える。 -/
theorem segreRowPolynomialMap_kernel_le :
    RingHom.ker (MvPolynomial.aeval (R := R) b).toRingHom ≤
      RingHom.ker (segreRowPolynomialMap (R := R) a b i).toRingHom := by
  classical
  intro p hp
  change segreRowPolynomialMap (R := R) a b i p = 0
  have hK := degreeOne_aeval_kernel_homogeneous b H hb
  rw [← DirectSum.sum_support_decompose (MvPolynomial.homogeneousSubmodule κ R) p, map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  apply segreCoordinateProjection_row_zero a b i
  · exact (MvPolynomial.mem_homogeneousSubmodule n _).mp
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule κ R) p n).property
  · exact hK.mem_iff.mp hp n

/-- 次数一の全射表示を使い、行の写像を実際の因子へ降ろす。 -/
def segreRowFromFactor (hs : Function.Surjective (MvPolynomial.aeval (R := R) b)) :
    B →ₐ[R] SegreCoordinateRing (R := R) a b :=
  AlgHom.liftOfSurjective (MvPolynomial.aeval (R := R) b) hs
    (segreRowPolynomialMap (R := R) a b i) (segreRowPolynomialMap_kernel_le a b i H hb)

/-- 因子の次数一生成元の像は、同じ行の座標。 -/
theorem segreRowFromFactor_generator
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) b)) (l : κ) :
    segreRowFromFactor a b i H hb hs (b l) =
      segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, l)) := by
  rw [← MvPolynomial.aeval_X (R := R) (f := b) l]
  change AlgHom.liftOfSurjective _ hs _ _ (MvPolynomial.aeval b (MvPolynomial.X l)) = _
  rw [AlgHom.liftOfSurjective_apply]
  simp [segreRowPolynomialMap]

end SerrePositivity.AlgebraicGeometry
