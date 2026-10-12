module

public import SerrePositivity.CommutativeAlgebra.FiniteLengthValue

public import SerrePositivity.CommutativeAlgebra.GradedLinearMap
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # 次数一の写像と Hilbert 級数の漸化式

核・余核の各次数の長さから、`(1-X)H_M = H_coker - X H_ker` を導く。
次数ごとの有限長性だけを使い、Hilbert–Serre の有理型表示は使わない。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable (N : ℕ → Submodule R M) [Decomposition N]

/-- 各次数の長さを係数とする級数。 -/
def lengthSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((Module.length R (N n)).toNat : ℚ)

/-- 各次数の元を含む部分加群への単射。 -/
def submoduleGradeInclusion (S : Submodule R M) (n : ℕ) :
    submoduleGrade N S n →ₗ[R] N n where
  toFun x := ⟨x.1.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Decomposition N] in
lemma submoduleGradeInclusion_injective (S : Submodule R M) (n : ℕ) :
    Function.Injective (submoduleGradeInclusion N S n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : N n => (z : M)) h

variable (hfinite : ∀ n, IsFiniteLength R (N n))

omit [Decomposition N] in
include hfinite in
lemma finiteLength_submoduleGrade (S : Submodule R M) (n : ℕ) :
    IsFiniteLength R (submoduleGrade N S n) :=
  (hfinite n).of_injective (f := submoduleGradeInclusion N S n)
    (submoduleGradeInclusion_injective N S n)

omit [Decomposition N] in
include hfinite in
lemma finiteLength_quotientGrade (S : Submodule R M) (n : ℕ) :
    IsFiniteLength R (quotientGrade N S n) := by
  let f : N n →ₗ[R] quotientGrade N S n :=
    (S.mkQ.comp (N n).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (hfinite n).of_surjective (f := f) hf

variable (f : M →ₗ[R] M)
variable (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + 1))

include hfinite hdegree

/-- 四項完全列の長さの加法性。 -/
lemma component_length_identity (n : ℕ) :
    ((Module.length R (N (n + 1))).toNat : ℚ) +
      ((Module.length R (submoduleGrade N f.ker n)).toNat : ℚ) =
    ((Module.length R (N n)).toNat : ℚ) +
      ((Module.length R (quotientGrade N f.range (n + 1))).toNat : ℚ) := by
  let d := componentMap N f hdegree n
  let g := quotientComponent N f (n + 1)
  have h1q : ((Module.length R (N n)).toNat : ℚ) =
      ((Module.length R d.ker).toNat : ℚ) + ((Module.length R d.range).toNat : ℚ) := by
    exact_mod_cast lengthNat_ker_add_range d (hfinite n)
  have h2q : ((Module.length R (N (n + 1))).toNat : ℚ) =
      ((Module.length R g.ker).toNat : ℚ) +
        ((Module.length R (quotientGrade N f.range (n + 1))).toNat : ℚ) := by
    exact_mod_cast lengthNat_add_of_exact g.ker.subtype g
      (Submodule.subtype_injective _) (quotientComponent_surjective N f (n + 1))
      (LinearMap.exact_subtype_ker_map g) (hfinite (n + 1))
  rw [(componentMap_quotientComponent_exact N f hdegree n).linearMap_ker_eq] at h2q
  rw [(kernelGradeEquiv N f hdegree n).length_eq]
  linarith

omit hfinite in
/-- 第零次には流入する写像がないので、余核の第零次は元の第零次に等しい。 -/
lemma length_quotientGrade_zero : Module.length R (quotientGrade N f.range 0) =
    Module.length R (N 0) :=
  (LinearEquiv.ofBijective (quotientComponent N f 0)
    ⟨quotientComponent_zero_injective N f hdegree,
      quotientComponent_surjective N f 0⟩).length_eq.symm

/-- 次数一の写像の核・余核による Hilbert 級数の漸化式。 -/
theorem one_sub_X_mul_lengthSeries :
    (1 - PowerSeries.X) * lengthSeries N =
      lengthSeries (quotientGrade N f.range) -
        PowerSeries.X * lengthSeries (submoduleGrade N f.ker) := by
  ext n
  cases n with
  | zero =>
    simp [lengthSeries, length_quotientGrade_zero N f hdegree]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      lengthSeries, PowerSeries.coeff_mk]
    have h := component_length_identity N hfinite f hdegree n
    linarith

end SerrePositivity.HilbertSerre
