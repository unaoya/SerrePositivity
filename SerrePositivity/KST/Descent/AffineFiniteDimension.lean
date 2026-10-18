module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# 有限型アフィン対象の有限次元上界

## 概要
Noether 基底環の次元上界から有限型代数の自然数の次元上界を構成する。

## 方針
有限変数多項式環からの全射と、その Noether 次元公式を使う。
局所 Noether 基底では極大イデアルの生成元数による上界を供給する。

## 規約
一般の Noether 環が有限次元とは主張しない。基底の次元条件を明示する。

## 使われ方
論文 定理 3.1・補題 3.2 のアフィン Čech 各段の次元帰納への入力。
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
  [IsNoetherianRing A] [Algebra.FiniteType A T]

/-- 概要：有限型代数の Spec に自然数の次元上界が存在する（論文 定理 3.1）。
方針：有限変数多項式環からの全射と dim A[X₁,…,Xₙ] = dim A + n を使う。
規約：基底 A の自然数上界を明示し、商が零環の場合も含む。
使われ方：有限型アフィン表示の次元上界の供給。 -/
theorem finiteType_spec_dimension_bound (d : ℕ)
    (bound : topologicalKrullDim (Spec (.of A)) ≤ d) :
    ∃ e : ℕ, topologicalKrullDim (Spec (.of T)) ≤ e := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A T)
  refine ⟨d + n, ?_⟩
  have hA : ringKrullDim A ≤ d := by
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A ▸ bound)
  change topologicalKrullDim (PrimeSpectrum T) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  calc
    ringKrullDim T ≤ ringKrullDim (MvPolynomial (Fin n) A) :=
      ringKrullDim_le_of_surjective φ.toRingHom hφ
    _ = ringKrullDim A + n := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
      simp
    _ ≤ (d : WithBot ℕ∞) + n := add_le_add hA le_rfl
    _ = (d + n : ℕ) := (Nat.cast_add d n).symm

omit [CommRing T] [Algebra A T] [Algebra.FiniteType A T] in
/-- 概要：局所 Noether 基底の Spec の具体的な次元上界（論文 定理 3.1）。
方針：Krull の高さ定理による極大イデアルの生成元数の上界を使う。
規約：局所性と Noether 性を明示し、一般の Noether 環には適用しない。
使われ方：既存の theorem_3_1_K0 の基底仮定から次元帰納の始点を供給する。 -/
theorem localNoether_spec_dimension_bound [IsLocalRing A] :
    topologicalKrullDim (Spec (.of A)) ≤ (IsLocalRing.maximalIdeal A).spanFinrank := by
  change topologicalKrullDim (PrimeSpectrum A) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_le_spanFinrank_maximalIdeal A

/-- 概要：局所 Noether 基底上の有限型代数の Spec は有限次元（論文 補題 3.2）。
方針：極大イデアルの生成元数の上界と有限型代数の上界を組み合わせる。
規約：上界を自然数として実際に供給し、追加の有限次元仮定に残さない。
使われ方：アフィン Čech 各段の座標環への次元帰納。 -/
theorem localNoether_finiteType_spec_dimension_bound [IsLocalRing A] :
    ∃ e : ℕ, topologicalKrullDim (Spec (.of T)) ≤ e :=
  finiteType_spec_dimension_bound _ (localNoether_spec_dimension_bound (A := A))

end SerrePositivity.KST.Descent
