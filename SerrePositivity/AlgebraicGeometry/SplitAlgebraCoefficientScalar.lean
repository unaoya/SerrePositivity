module

public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientIdeal
public import Mathlib.RingTheory.Ideal.Operations

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の代数イデアルの基礎環の元倍と係数イデアル。
方針：係数表示の線形性と単項イデアルの積への所属判定を使う。
規約：この計算自体には係数表示の分裂は不要。
使われ方：正則な共通因子を除いたイデアルの係数が単位イデアルを生成することを示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：基礎環の元を代数イデアルに掛ける操作は係数イデアルと可換。
方針：一方向は単項イデアルの積の表示、逆方向は係数の生成集合の span の帰納法で示す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、境界元の正則性も分裂表示も不要。
使われ方：共通因子を除いたイデアルの係数イデアルを計算する。
-/
theorem splitAlgebraCoefficientIdeal_scalar {R B ι : Type*}
    [CommRing R] [CommRing B] [Algebra R B]
    (e : B →ₗ[R] (ι →₀ R)) (c : R) (J : Ideal B) :
    splitAlgebraCoefficientIdeal e (Ideal.span {algebraMap R B c} * J) =
      Ideal.span {c} * splitAlgebraCoefficientIdeal e J := by
  have he : ∀ b i, e (algebraMap R B c * b) i = c * e b i := by
    intro b i
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply le_antisymm
  · apply (finsuppCoefficientIdeal_le_iff _ _).mpr
    rintro x ⟨b, hb, rfl⟩ i
    obtain ⟨d, hd, hbd⟩ := Ideal.mem_span_singleton_mul.mp hb
    rw [← hbd, he]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c)
      (mem_finsuppCoefficientIdeal (s := e '' (J : Set B)) ⟨d, hd, rfl⟩ i)
  · rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, ⟨b, hb, rfl⟩, i, rfl⟩ := hx
      rw [← he]
      exact mem_finsuppCoefficientIdeal
        (s := e '' (Ideal.span {algebraMap R B c} * J : Set B))
        ⟨algebraMap R B c * b,
          Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hb, rfl⟩ i
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [mul_add] using Ideal.add_mem _ hx hy
    | smul r x _ hx =>
      simpa only [smul_eq_mul, mul_left_comm c r x] using Ideal.mul_mem_left _ r hx

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
