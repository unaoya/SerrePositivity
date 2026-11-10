module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePD
public import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPModPBlocks
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.Powers
public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-!
# 分冪表示関係の剰余 Koszul 複体

## 概要
p が零なら、正則列に沿う分冪表示の関係列は Koszul 正則（BS 著者版 Lemma 2.38）。

## 方針
切断多項式環上で関係列を計算し、Tor の対称性で元の列の p 乗の Koszul 複体と比べる。

## 規約
正則性は Koszul 正則性。係数環の Noether 性は仮定しない。

## 使われ方
一般の分冪表示環の p 正則性と高次 Tor の消滅。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical TensorProduct

universe u

namespace SerrePositivity.BhattScholze

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

local notation "P" => MvPolynomial (Fin r) A
local notation "G" => DividedPowerAlgebra A (Fin r →₀ A)
local notation "g" => (fun i : Fin r => (MvPolynomial.X i : P) - MvPolynomial.C (f i))
local notation "J" => Ideal.span (Set.range g)
local notation "φ" => AlgHom.toRingHom (MvPolynomial.aeval f)

/-- 概要：各変数を指定した係数に等しくする関係式の Koszul 分解。
方針：各座標のモニック一次多項式に既存の正則性を適用する。
規約：BS 著者版 Lemma 2.38 の評価射の模型。
使われ方：分冪包の Tor 計算。 -/
theorem evaluationRelations_regular : IsKoszulResolution g := by
  simpa [Andre.monicRelation] using
    (Andre.monicRelation_fin_isKoszulResolution
      (fun i : Fin r => Polynomial.X - Polynomial.C (f i))
      (fun i => Polynomial.monic_X_sub_C (f i)) id Function.injective_id)

private def evaluationRelationsQuotient : (P ⧸ J) ≃+* A := by
  let q := Ideal.Quotient.mk J
  let e : (P ⧸ J) →+* A := Ideal.Quotient.lift J φ (by
    have h : J ≤ RingHom.ker φ := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change φ (g i) = 0
      simp
    exact fun _ x => h x)
  let v := q.comp (MvPolynomial.C : A →+* P)
  have he : e.comp q = φ := by
    apply RingHom.ext
    intro x
    exact Ideal.Quotient.lift_mk _ _ _
  have hv : v.comp φ = q := by
    apply MvPolynomial.ringHom_ext'
    · apply RingHom.ext
      intro a
      change v (φ (MvPolynomial.C a)) = q (MvPolynomial.C a)
      rw [MvPolynomial.aeval_C]
      rfl
    · intro i
      change v (φ (MvPolynomial.X i)) = q (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X]
      change q (MvPolynomial.C (f i)) = q (MvPolynomial.X i)
      symm
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  refine RingEquiv.ofRingHom e v ?_ ?_
  · apply RingHom.ext
    intro a
    change e (q (MvPolynomial.C a)) = a
    rw [← RingHom.comp_apply, he, MvPolynomial.aeval_C]
  · apply RingHom.ext
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (e (q x)) = q x
    rw [← RingHom.comp_apply, he, ← RingHom.comp_apply, hv]

private theorem evaluationRelationsQuotient_mk (x : P) :
    evaluationRelationsQuotient f (Ideal.Quotient.mk J x) = φ x := by
  unfold evaluationRelationsQuotient
  exact Ideal.Quotient.lift_mk _ _ _

/-- 概要：指定した係数への評価の商は、評価射で作用する係数環。
方針：商と係数の標準射が互いに逆で、係数拡大と両立する。
規約：BS 著者版 Lemma 2.38 の評価射の模型。
使われ方：Koszul 分解から Tor を計算する。 -/
def evaluationRelationsQuotientAlgEquiv :
    letI : Algebra P A := (φ).toAlgebra
    (P ⧸ J) ≃ₐ[P] A := by
  letI : Algebra P A := (φ).toAlgebra
  exact { __ := evaluationRelationsQuotient f
          commutes' := evaluationRelationsQuotient_mk f }


variable {p : ℕ} [Fact p.Prime]

local notation "T" => P ⧸ truncatedPolynomialIdeal A (Fin r) p
local notation "q" => Ideal.Quotient.mk (truncatedPolynomialIdeal A (Fin r) p)
local notation "v" => (fun i : Fin r => (MvPolynomial.X i : P) ^ p)

private theorem variablePowers_regular : IsKoszulResolution v := by
  simpa [Andre.monicRelation, Polynomial.eval₂_pow] using
    (Andre.monicRelation_fin_isKoszulResolution
      (fun _ : Fin r => (Polynomial.X : Polynomial A)^p)
      (fun _ => Polynomial.monic_X.pow p) id Function.injective_id)

private theorem truncatedEvaluationRelations_regular (hf : IsKoszulResolution f) :
    IsKoszulResolution (q ∘ g) := by
  letI : Algebra P A := (φ).toAlgebra
  refine ⟨?_, koszulComplex_homology_zero_equiv _⟩
  intro i hi
  by_cases hip : 0 < i
  · exact koszulComplex_isZero_homology_of_pos _ i hip
  have hn : i = -(i.natAbs : ℤ) := by omega
  have hpow : algebraMap P A ∘ v = fun j => f j ^ p := by
    funext j
    change φ ((MvPolynomial.X j : P)^p) = _
    rw [map_pow, MvPolynomial.aeval_X]
  have e₁ := algebraKoszulTorComparison (C := T) g (evaluationRelations_regular f) i.natAbs
  have e₂ := algebraKoszulTorComparison (C := A) v (variablePowers_regular (p := p)) i.natAbs
  rw [hpow, ← hn] at e₂
  rw [← hn] at e₁
  let F := (Tor (ModuleCat P) i.natAbs).obj (ModuleCat.of P T)
  let e₃ := F.mapIso (evaluationRelationsQuotientAlgEquiv f).toLinearEquiv.toModuleIso
  let e₄ := (torComm i.natAbs (ModuleCat.of P T) (ModuleCat.of P A)).toModuleIso
  have hz := ModuleCat.isZero_iff_subsingleton.mp ((hf.pow (fun _ => p)).isZero i hi)
  rw [ModuleCat.isZero_iff_subsingleton]
  letI : Subsingleton ((ModuleCat.restrictScalars (algebraMap P A)).obj
    ((koszulComplex (fun j => f j ^ p)).homology i)) := hz
  exact (e₁.symm ≪≫ e₃ ≪≫ e₄ ≪≫ e₂).toLinearEquiv.injective.subsingleton

/-- 概要：標数 p で分冪表示関係の列は Koszul 正則。
方針：切断多項式上の計算を、自由分冪代数への平坦な底変換で移す。
規約：入力は任意の有限 Koszul 正則列（BS 著者版 Lemma 2.38）。
使われ方：整数係数の分冪表示環の p 正則性。 -/
theorem dpFamilyRelations_isKoszulResolution_of_prime_zero
    (hp : (p : A) = 0) (hf : IsKoszulResolution f) :
    IsKoszulResolution (fun i =>
      DividedPowerAlgebra.dp A 1 (Finsupp.single i 1 : Fin r →₀ A) - algebraMap A G (f i)) := by
  letI : Algebra T G := freeDPTruncatedAlgebra hp
  haveI : Module.Free T G := freeDPTruncated_moduleFree hp
  let s := algebraMap T G ∘ (q ∘ g)
  have he : s = fun i =>
      DividedPowerAlgebra.dp A 1 (Finsupp.single i 1 : Fin r →₀ A) - algebraMap A G (f i) := by
    funext i
    change freeDPTruncatedMap hp (q (g i)) = _
    rw [freeDPTruncatedMap_mk]
    simp
  rw [← he]
  refine ⟨?_, koszulComplex_homology_zero_equiv _⟩
  intro i hi
  have hz := (truncatedEvaluationRelations_regular (p := p) f hf).isZero i hi
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
  letI := hz
  exact (flatBaseChangeKoszulHomologyEquiv T G (q ∘ g) i).injective.subsingleton

end SerrePositivity.BhattScholze
