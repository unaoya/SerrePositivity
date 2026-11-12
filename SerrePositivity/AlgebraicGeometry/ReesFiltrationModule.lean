module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.DirectSum.Module

/-!
概要：フィルター加群の Rees 加群を、その次数成分の直和と同一視する。
方針：Mathlib の多項式加群内の部分加群を使い、係数と単項式の写像で比較する。
規約：フィルトレーションの各成分は元の加群の部分加群とする。
使われ方：Rees 加群の有限性を射影 Čech 計算に渡し、次数ごとの写像を取り出す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Ideal R} (F : I.Filtration M)

/-- Rees 加群の一つの次数の係数を取り出す。 -/
def reesFiltrationCoeff (n : ℕ) : F.submodule →ₗ[R] F.N n where
  toFun p := ⟨p.val.coeff n, p.property n⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- フィルトレーションの一つの成分を Rees 加群の単項式に入れる。 -/
def reesFiltrationSingle (n : ℕ) : F.N n →ₗ[R] F.submodule where
  toFun m := ⟨PolynomialModule.lsingle R n m.val, by
    intro j
    by_cases h : n = j
    · subst j
      simpa [PolynomialModule.lsingle_apply] using m.property
    · simp only [PolynomialModule.lsingle_apply, h, ite_false]
      exact Submodule.zero_mem _⟩
  map_add' x y := Subtype.ext ((PolynomialModule.lsingle R n).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((PolynomialModule.lsingle R n).map_smul r x.val)

/-- Rees 加群の単項式の係数。 -/
theorem reesFiltrationSingle_coeff (n j : ℕ) (m : F.N n) :
    (reesFiltrationSingle F n m).val.coeff j = if n = j then m.val else 0 :=
  PolynomialModule.lsingle_apply n m.val j

/-- 各次数成分の直和から Rees 加群へ単項式を足し合わせる。 -/
def reesFiltrationAssemble : (⨁ n, F.N n) →ₗ[R] F.submodule :=
  DirectSum.toModule R ℕ F.submodule (reesFiltrationSingle F)

/-- 直和の一つの成分は、対応する単項式に写る。 -/
@[simp]
theorem reesFiltrationAssemble_of (n : ℕ) (m : F.N n) :
    reesFiltrationAssemble F (DirectSum.of (fun n ↦ F.N n) n m) =
      reesFiltrationSingle F n m :=
  DirectSum.toAddMonoid_of (fun n ↦ (reesFiltrationSingle F n).toAddMonoidHom) n m

/-- 直和から足した元の係数は、元の直和の同じ次数の成分。 -/
theorem reesFiltrationAssemble_coeff (z : ⨁ n, F.N n) (n : ℕ) :
    (reesFiltrationAssemble F z).val.coeff n = (z n).val := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    rw [reesFiltrationAssemble_of, reesFiltrationSingle_coeff]
    by_cases h : j = n
    · subst n
      simp
    · simp [DirectSum.of_apply, h]
  | add x y hx hy => simpa only [map_add, Submodule.coe_add,
      PolynomialModule.coeff_add, Finsupp.add_apply, DirectSum.add_apply] using congrArg₂ (· + ·) hx hy

/-- Rees 加群の単項式表示は一意。 -/
theorem reesFiltrationAssemble_injective : Function.Injective (reesFiltrationAssemble F) := by
  intro x y h
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  have hc := congrArg (fun p : F.submodule ↦ p.val.coeff n) h
  simpa only [reesFiltrationAssemble_coeff] using hc

/-- Rees 加群の元は、その有限個の係数を持つ単項式の和に等しい。 -/
theorem reesFiltration_sum_single (p : F.submodule) :
    (∑ n ∈ p.val.coeff.support, reesFiltrationSingle F n ⟨p.val.coeff n, p.property n⟩) = p := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change ∑ n ∈ p.val.coeff.support, PolynomialModule.single R n (p.val.coeff n) = p.val
  apply PolynomialModule.coeff_injective
  rw [PolynomialModule.coeff_sum]
  simp only [PolynomialModule.coeff_single]
  exact Finsupp.sum_single p.val.coeff

/-- Rees 加群の各元は、その有限個の係数を持つ単項式の和。 -/
theorem reesFiltrationAssemble_surjective : Function.Surjective (reesFiltrationAssemble F) := by
  classical
  intro p
  let z : ⨁ n, F.N n := ∑ n ∈ p.val.coeff.support,
    DirectSum.of (fun n ↦ F.N n) n ⟨p.val.coeff n, p.property n⟩
  refine ⟨z, ?_⟩
  change reesFiltrationAssemble F (∑ n ∈ p.val.coeff.support,
    DirectSum.of (fun n ↦ F.N n) n ⟨p.val.coeff n, p.property n⟩) = p
  simp only [map_sum, reesFiltrationAssemble_of]
  exact reesFiltration_sum_single F p

/-- フィルトレーションの各次数の直和と、Mathlib の Rees 加群の線形同型。 -/
def reesFiltrationDirectSumLinearEquiv : (⨁ n, F.N n) ≃ₗ[R] F.submodule :=
  LinearEquiv.ofBijective (reesFiltrationAssemble F)
    ⟨reesFiltrationAssemble_injective F, reesFiltrationAssemble_surjective F⟩

/-- Rees 環の斉次単項式は、加群の次数をその指数だけ上げる。 -/
theorem reesFiltration_monomial_smul_single (n j : ℕ) (r : R) (hr : r ∈ I ^ n)
    (m : F.N j) :
    (⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : reesAlgebra I) •
        reesFiltrationSingle F j m =
      reesFiltrationSingle F (n + j) ⟨r • m.val,
        F.pow_smul_le n j (Submodule.smul_mem_smul hr m.property)⟩ := by
  apply Subtype.ext
  exact PolynomialModule.monomial_smul_lsingle n r j m.val

/-- 安定なフィルトレーションの Rees 加群は Rees 環上有限生成。 -/
theorem reesFiltration_finite [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable) :
    Module.Finite (reesAlgebra I) F.submodule := by
  apply Module.Finite.of_fg
  exact (F.submodule_fg_iff_stable (fun n ↦ IsNoetherian.noetherian (F.N n))).mpr hF

end SerrePositivity.AlgebraicGeometry
