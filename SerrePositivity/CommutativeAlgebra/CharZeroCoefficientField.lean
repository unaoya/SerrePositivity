module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.Perfect

/-! # 剰余標数零の完備局所環の係数体

## 概要

剰余体が標数零の局所環 `A` は `ℚ` 代数である（`ratAlgebra_of_residueCharZero`）。
さらに `A` が完備なら、剰余写像 `A → k` は環準同型の切断を持つ
（係数体の存在、`exists_residue_section_of_charZero`）。

## 方針

`ℚ` 代数構造：非零整数の像は剰余体で消えないので `A` の単元であり、
`ℤ` の分数体の普遍性（`IsLocalization.lift`）で `ℚ → A` を作る。

係数体：`k` の `ℚ` 上の超越基底 `x` をとり、各 `x_i` を `A` へ持ち上げる。
多項式環からの評価写像は剰余体で単射なので、非零元は `A` の単元へ写り、
有理関数体 `K = ℚ(x)` からの写像 `K → A` に延びる。
標数零では `k / K` は分離代数的なので形式エタールであり、
`A` が完備なので `k → A/m` は `K` 上 `k → A` へ持ち上がる
（Mathlib の `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`）。

## 規約

Noether 性は仮定しない。係数体は存在定理として述べる。最後の持ち上げは Mathlib でも
存在定理としてしか公開されておらず、超越基底の選び方も標準的でないため、def にはしない。
`ℚ` 代数構造は、Mathlib の対応物（`MixedCharZero` の `algebraRat`）が private なので自前で作る。
Cohen の構造定理の等標数零の場合で、Mathlib への提出候補（mathlib-upstream の G5）。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（標数零の係数体の存在）。
剰余標数零の完備正則局所環を冪級数環と同一視するのに使う（`EqualCharZeroPositivity`）。
正標数の係数体（`CoefficientField`）とは独立である。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- 剰余標数零の局所環では、非零整数の像は単元である。 -/
theorem isUnit_intCast_of_residueCharZero
    (R : Type*) [CommRing R] [IsLocalRing R] [CharZero (ResidueField R)]
    {n : ℤ} (hn : n ≠ 0) : IsUnit (n : R) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa only [map_intCast, Int.cast_ne_zero] using hn

/-- 剰余標数零の局所環の `ℚ` 代数構造。非零整数の単元性から分数体の写像を作る。 -/
@[instance_reducible]
noncomputable def ratAlgebra_of_residueCharZero
    (R : Type*) [CommRing R] [IsLocalRing R] [CharZero (ResidueField R)] : Algebra ℚ R :=
  (IsLocalization.lift (S := ℚ) (g := Int.castRingHom R) fun n ↦
    isUnit_intCast_of_residueCharZero R (mem_nonZeroDivisors_iff_ne_zero.mp n.property)).toAlgebra

/-- **標数零の係数体**：剰余体が標数零の完備局所環では、剰余写像は環準同型の切断を持つ。
超越基底の持ち上げで有理関数体を埋め込み、残りの分離代数拡大は形式エタール性で持ち上げる。 -/
theorem exists_residue_section_of_charZero (A : Type u) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [CharZero (ResidueField A)] :
    ∃ g : ResidueField A →+* A, (residue A).comp g = RingHom.id _ := by
  classical
  let : Algebra ℚ A := ratAlgebra_of_residueCharZero A
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' ℚ (ResidueField A)
  choose y hy using fun i ↦ residue_surjective (x i)
  -- 剰余写像と評価写像の両立
  have hres : (residue A).comp (MvPolynomial.aeval (R := ℚ) y).toRingHom =
      (MvPolynomial.aeval (R := ℚ) x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact congrFun (congrArg DFunLike.coe (Subsingleton.elim
        (((residue A).comp (MvPolynomial.aeval (R := ℚ) y).toRingHom).comp MvPolynomial.C)
        ((MvPolynomial.aeval (R := ℚ) x).toRingHom.comp MvPolynomial.C))) r
    · intro i
      simp [hy]
  have hinj := algebraicIndependent_iff_injective_aeval.mp hx.1
  have hunit : ∀ a : nonZeroDivisors (MvPolynomial ι ℚ),
      IsUnit ((MvPolynomial.aeval (R := ℚ) y).toRingHom a) := by
    intro a
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [← RingHom.comp_apply, hres]
    exact (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero a.2)
  let F := FractionRing (MvPolynomial ι ℚ)
  let φ : F →+* A := IsLocalization.lift (M := nonZeroDivisors (MvPolynomial ι ℚ)) hunit
  let K := IntermediateField.adjoin ℚ (Set.range x)
  -- 有理関数体と `K = ℚ(x)` の同型（`ℚ` 代数構造の食い違いを避けて環同型として扱う）
  let e : F ≃+* K :=
    @AlgEquiv.toRingEquiv ℚ F K _ _ _ OreLocalization.instAlgebra _ hx.1.aevalEquivField
  have he : ∀ a : MvPolynomial ι ℚ,
      ((e (algebraMap (MvPolynomial ι ℚ) F a) : K) : ResidueField A) =
        MvPolynomial.aeval x a := fun a ↦
    hx.1.aevalEquivField_algebraMap_apply_coe a
  -- `K = ℚ(x)` から `A` への持ち上げ
  let ψ : K →+* A := φ.comp e.symm.toRingHom
  have hψ : ∀ c : K, residue A (ψ c) = (c : ResidueField A) := by
    have h : (residue A).comp φ = K.val.toRingHom.comp e.toRingHom := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι ℚ))
      rw [RingHom.comp_assoc, IsLocalization.lift_comp, hres]
      ext a
      · simp
      · exact (he _).symm
    intro c
    have := RingHom.congr_fun h (e.symm c)
    simpa [ψ] using this
  let : Algebra K A := ψ.toAlgebra
  have : Algebra.IsAlgebraic K (ResidueField A) := hx.isAlgebraic_field
  have : Algebra.FormallyEtale K (ResidueField A) := Algebra.FormallyEtale.of_isSeparable _ _
  -- 剰余体から `A/m` への `K` 上の写像
  let f : ResidueField A →ₐ[K] A ⧸ maximalIdeal A :=
    { toRingHom := RingHom.id _
      commutes' := fun c ↦ by
        change (c : ResidueField A) = Ideal.Quotient.mk (maximalIdeal A) (ψ c)
        exact (hψ c).symm }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f
  refine ⟨g.toRingHom, RingHom.ext fun z ↦ ?_⟩
  exact congrArg (fun h : ResidueField A →ₐ[K] A ⧸ maximalIdeal A ↦ h z) hg

end SerrePositivity
