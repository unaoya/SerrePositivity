module

public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Normality
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.Paper.Section2.Lemma2_2
public import SerrePositivity.CommutativeAlgebra.HenselianFinite
public import SerrePositivity.FieldTheory.SeparableBaseChange
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure

/-!
# 正規化基底と群作用付き拡大の同時構成

完備局所整域に補題2.2を適用して正則な基底を選び、その基底を保ったままガロア閉包へ上げる。
新しい整域の自己同型群の不変環は選んだ基底に一致する。
有限性・完備性・剰余体の一致を構成し、冪級数環と Witt 冪級数環の表示も新しい剰余体へ移す。
引用への依存は補題2.2の正規化に残る。正則パラメータの正則性は証明済み。
前段（`GaloisNormalizationBasePart`）では、有限で生成点で分離的な整域拡大 `A → D` を、分数体拡大の正規閉包の中の
`A` の整閉包へ埋め込み、有限群作用を持つ完備局所整域で不変環が `A`、剰余体が変わらないものを作る。
`IsIntegrallyClosed A` は明示的な仮定で、正則局所環の正規性の証明は含めない。
-/

@[expose] public section

universe u v

section GaloisNormalizationBasePart


namespace SerrePositivity

open IsLocalRing

set_option synthInstance.maxSize 2048

/-- 分離拡大の正規閉包は分離的である。
各埋め込みの像が分離的であることを確認し、それらの合成体としての定義を使う。 -/
theorem isSeparable_normalClosure
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L Ω) := by
  have (f : L →ₐ[K] Ω) : Algebra.IsSeparable K f.fieldRange :=
    Algebra.IsSeparable.of_algHom K L f.equivFieldRange.symm.toAlgHom
  unfold IntermediateField.normalClosure
  infer_instance

/-- 正規な完備ネーター局所基底上の有限分離整域拡大を、ガロア群作用付きの有限局所拡大へ上げる。
結論の自己同型群は有限で、不変元は全て基底から来る。基底の剰余体が代数閉なので、
新しい環の剰余体への基底からの写像も全射となる。整閉包の有限性は有限分離拡大に関する
トレースの一般論で十分であり、優秀環の一般論は使わない。 -/
theorem exists_galoisNormalization_of_normal_base
    (A D : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsAlgClosed (ResidueField A)]
    [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
      (_ : IsAdicComplete (maximalIdeal B) B) (_ : Algebra A B) (_ : Algebra D B)
      (_ : IsScalarTower A D B),
      Module.Finite A B ∧ Module.Finite D B ∧
      Function.Injective (algebraMap D B) ∧
      Function.Surjective ((residue B).comp (algebraMap A B)) ∧
      (∀ b : B, ((minpoly A b).map (algebraMap A (FractionRing A))).Separable) ∧
      Finite (B ≃ₐ[A] B) ∧
      (∀ b : B, (∀ g : B ≃ₐ[A] B, g b = b) → b ∈ Set.range (algebraMap A B)) := by
  classical
  let : Module.IsTorsionFree A D := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := finiteDimensional_fractionRing_of_finite A D K L
  let : Algebra.IsSeparable K L := isSeparable_fractionRing_of_separable_minpoly A D K L hsep
  let Ω := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L Ω
  let : Algebra.IsSeparable K E := isSeparable_normalClosure K L Ω
  let : IsGalois K E := ⟨⟩
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra D E := ((algebraMap L E).comp (algebraMap D L)).toAlgebra
  let : IsScalarTower D L E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A L E := IsScalarTower.to₁₃₄ A K L E
  let : IsScalarTower A D E := IsScalarTower.to₁₂₄ A D L E
  let B := integralClosure A E
  let f : D →ₐ[A] B :=
    (IsScalarTower.toAlgHom A D E).codRestrict B (fun d ↦
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A D E)
        ((algebraMap L E).injective.comp (IsFractionRing.injective D L))).mpr
        (Algebra.IsIntegral.isIntegral (R := A) d))
  let : Algebra D B := f.toRingHom.toAlgebra
  let : IsScalarTower A D B := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  let : IsScalarTower D B E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite A B := IsIntegralClosure.finite A K E B
  let : Module.Finite D B := Module.Finite.right A D B
  let : IsFractionRing B E := IsIntegralClosure.isFractionRing_of_finite_extension A K E B
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let : Finite (B ≃ₐ[A] B) :=
    Finite.of_equiv (E ≃ₐ[K] E) (galRestrict A K E B).toEquiv
  let : IsLocalRing B := isLocalRing_finite_domain_of_complete A B
  let : IsAdicComplete (maximalIdeal B) B := isAdicComplete_finite_local_algebra (R := A) B
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    residue_surjective_of_finite_of_isAlgClosed A B, ?_, inferInstance, ?_⟩
  · intro x y hxy
    exact ((algebraMap L E).injective.comp (IsFractionRing.injective D L))
      (congrArg (algebraMap B E) hxy)
  · exact (separable_minpoly_iff_fractionRing A B K E).mpr inferInstance
  · exact (Algebra.isInvariant_of_isGalois' A K E B).1

end SerrePositivity

end GaloisNormalizationBasePart

namespace SerrePositivity.Section5

open IsLocalRing

set_option synthInstance.maxSize 2048

/-- 係数環の同型を形式的冪級数へ係数ごとに適用する。変数は保つ。 -/
private def powerSeriesMapEquiv {k l : Type u} [CommRing k] [CommRing l]
    (σ : Type v) (e : k ≃+* l) : MvPowerSeries σ k ≃+* MvPowerSeries σ l where
  __ := MvPowerSeries.map e.toRingHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp

/-- 剰余体の同型を Witt ベクトル環の同型へ移す。 -/
private noncomputable def wittMapEquiv {k l : Type u} [CommRing k] [CommRing l]
    (p : ℕ) [Fact p.Prime] (e : k ≃+* l) : WittVector p k ≃+* WittVector p l :=
  RingEquiv.ofBijective (WittVector.map e.toRingHom)
    ⟨WittVector.map_injective _ e.injective, WittVector.map_surjective _ e.surjective⟩

/-- 完備局所整域から、正規化基底とそれを固定する有限群作用付き拡大を同時に選ぶ。
基底は先に補題2.2で選び、ガロア閉包の後で選び直さない。
返す具体的な基底表示は拡大後の剰余体を係数とするので、定理2.5へ直接渡せる。 -/
theorem exists_regular_galoisNormalization
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [IsAlgClosed (ResidueField D)]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A)
      (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
      (_ : IsAdicComplete (maximalIdeal B) B) (_ : Algebra A B) (_ : Algebra D B),
      Module.Finite A B ∧ Module.Finite D B ∧
      Function.Injective (algebraMap A B) ∧ Function.Injective (algebraMap D B) ∧
      Function.Surjective ((residue B).comp (algebraMap A B)) ∧
      Function.Surjective ((residue B).comp (algebraMap D B)) ∧
      (∀ b : B, ((minpoly A b).map (algebraMap A (FractionRing A))).Separable) ∧
      Finite (B ≃ₐ[A] B) ∧
      (∀ b : B, (∀ g : B ≃ₐ[A] B, g b = b) → b ∈ Set.range (algebraMap A B)) ∧
      ringKrullDim A = h ∧
      ∃ t : Fin h → A, Ideal.span (Set.range t) = maximalIdeal A ∧
        ((CharP B p ∧ ∃ f : A ≃+* MvPowerSeries (Fin h) (ResidueField B),
            ∀ j, f (t j) = MvPowerSeries.X j) ∨
         (CharZero B ∧ t ⟨0, hpos⟩ = (p : A) ∧
            ∃ f : A ≃+* MvPowerSeries {j : Fin h // (j : ℕ) ≠ 0}
                (WittVector p (ResidueField B)),
              ∀ (j : Fin h) (hj : (j : ℕ) ≠ 0), f (t j) = MvPowerSeries.X ⟨j, hj⟩)) := by
  obtain ⟨A, aRing, aReg, aComplete, aAlg, hinj, hfinite, hsep, hres,
      hdimA, t, ht, _, hbase⟩ := Section2.lemma_2_2 D hdim hpos p
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  let er := residueFieldEquiv_of_surjective D hres
  let : IsAlgClosed (ResidueField A) := IsAlgClosed.of_ringEquiv _ _ er.symm
  obtain ⟨B, bRing, bDomain, bLocal, bComplete, abAlg, dbAlg, adbTower,
      hAB, hDB, hinjDB, hresAB, hsepB, hG, hfix⟩ :=
    exists_galoisNormalization_of_normal_base A D hinj hsep
  let := hDB
  have hresDB := residue_surjective_of_finite_of_isAlgClosed D B
  let eDB := residueFieldEquiv_of_surjective B hresDB
  have hinjAB : Function.Injective (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A D B]
    exact hinjDB.comp hinj
  refine ⟨A, B, aRing, aReg, aComplete, bRing, bDomain, bLocal, bComplete, abAlg, dbAlg,
    hAB, hDB, hinjAB, hinjDB, hresAB, hresDB, hsepB, hG, hfix, hdimA, t, ht, ?_⟩
  rcases hbase with ⟨hpD, f, hf⟩ | ⟨hzeroD, htp, f, hf⟩
  · let := hpD
    refine Or.inl ⟨charP_of_injective_algebraMap hinjDB p,
      f.trans (powerSeriesMapEquiv (Fin h) eDB), ?_⟩
    intro j
    change MvPowerSeries.map eDB.toRingHom (f (t j)) = _
    rw [hf, MvPowerSeries.map_X]
  · let := hzeroD
    refine Or.inr ⟨charZero_of_injective_algebraMap hinjDB, htp,
      f.trans (powerSeriesMapEquiv _ (wittMapEquiv p eDB)), ?_⟩
    intro j hj
    change MvPowerSeries.map (wittMapEquiv p eDB).toRingHom (f (t j)) = _
    rw [hf j hj, MvPowerSeries.map_X]

end SerrePositivity.Section5
