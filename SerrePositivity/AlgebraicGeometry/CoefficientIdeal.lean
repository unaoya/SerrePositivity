module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の自由な直和の係数計算。
方針：有限台の展開により、線形写像が係数のイデアルへの所属を保つことを示す。
規約：直和の添字集合の有限性も環の Noether 性も仮定しない。
使われ方：自由加群の直和因子となる代数で、イデアルの係数から基底の中心を作る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] {ι κ : Type*}

/--
概要：自由な直和の線形写像は、全係数が一つのイデアルに属する条件を保つ。
方針：元を有限個の単項ベクトルに展開して、係数倍と有限和の閉性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、異なる添字集合間の写像も許す。
使われ方：代数の乗法を直和の線形自己写像へ延長して係数イデアルを比較する。
-/
theorem finsupp_linearMap_coeff_mem (T : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (I : Ideal R) (x : ι →₀ R) (hx : ∀ i, x i ∈ I) (j : κ) :
    T x j ∈ I := by
  classical
  have hsum : T x = ∑ i ∈ x.support, x i • T (Finsupp.single i 1) := by
    calc
      T x = T (x.sum fun i r => Finsupp.single i r) := by rw [Finsupp.sum_single]
      _ = ∑ i ∈ x.support, x i • T (Finsupp.single i 1) := by
        simp only [Finsupp.sum, map_sum, ← map_smul, Finsupp.smul_single,
          smul_eq_mul, mul_one]
  rw [hsum]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact I.sum_mem fun i _ => I.mul_mem_right _ (hx i)

/--
概要：直和のベクトルの集合の全係数が生成するイデアル。
方針：集合に属するベクトルと係数の添字を同時に走らせて span を取る。
規約：KST §5、Stacks 0810, Lemma 38.30.2、零係数も生成集合に含める。
使われ方：代数のイデアルの係数イデアルの定義。
-/
def finsuppCoefficientIdeal (s : Set (ι →₀ R)) : Ideal R :=
  Ideal.span {r | ∃ x ∈ s, ∃ i, x i = r}

/--
概要：元の集合の各係数は係数イデアルに属する。
方針：span の生成元として所属を示す。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：係数イデアルの最小性と有限生成性の証明。
-/
theorem mem_finsuppCoefficientIdeal {s : Set (ι →₀ R)} {x : ι →₀ R}
    (hx : x ∈ s) (i : ι) : x i ∈ finsuppCoefficientIdeal s :=
  Ideal.subset_span ⟨x, hx, i, rfl⟩

/--
概要：係数イデアルの包含は全係数の所属と同値。
方針：span の普遍性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：乗法・線形写像に沿う係数イデアルの比較。
-/
theorem finsuppCoefficientIdeal_le_iff (s : Set (ι →₀ R)) (I : Ideal R) :
    finsuppCoefficientIdeal s ≤ I ↔ ∀ x ∈ s, ∀ i, x i ∈ I := by
  constructor
  · intro h x hx i
    exact h (mem_finsuppCoefficientIdeal hx i)
  · intro h
    apply Ideal.span_le.mpr
    rintro r ⟨x, hx, i, rfl⟩
    exact h x hx i

/--
概要：線形写像による集合の像の係数イデアルは元の係数イデアルに含まれる。
方針：元の各係数の所属に有限台の線形写像の計算を適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、線形写像の単射性は不要。
使われ方：自由な直和で表した乗法による係数イデアルの不変性。
-/
theorem finsuppCoefficientIdeal_image_le (T : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (s : Set (ι →₀ R)) : finsuppCoefficientIdeal (T '' s) ≤ finsuppCoefficientIdeal s := by
  apply (finsuppCoefficientIdeal_le_iff _ _).mpr
  rintro y ⟨x, hx, rfl⟩ j
  exact finsupp_linearMap_coeff_mem T _ x (mem_finsuppCoefficientIdeal hx) j

/--
概要：有限個の直和ベクトルの係数イデアルは有限生成。
方針：各ベクトルの有限台の係数を集め、それ以外の係数は零であることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、直和全体の有限階数性は不要。
使われ方：代数の有限生成イデアルから作る基底上の中心の有限生成性。
-/
theorem finsuppCoefficientIdeal_fg {s : Set (ι →₀ R)} (hs : s.Finite) :
    (finsuppCoefficientIdeal s).FG := by
  classical
  let t : Finset R := hs.toFinset.biUnion fun x => x.support.image x
  have hspan : finsuppCoefficientIdeal s = Ideal.span (t : Set R) := by
    apply le_antisymm
    · apply (finsuppCoefficientIdeal_le_iff _ _).mpr
      intro x hx i
      by_cases hi : i ∈ x.support
      · exact Ideal.subset_span (Finset.mem_biUnion.mpr
          ⟨x, hs.mem_toFinset.mpr hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      · rw [Finsupp.notMem_support_iff.mp hi]
        exact Ideal.zero_mem _
    · apply Ideal.span_le.mpr
      intro r hr
      obtain ⟨x, hx, hr⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact mem_finsuppCoefficientIdeal (hs.mem_toFinset.mp hx) i
  rw [hspan]
  exact Submodule.fg_span t.finite_toSet

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
