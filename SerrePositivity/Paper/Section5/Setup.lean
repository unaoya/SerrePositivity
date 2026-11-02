module

public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Normality
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.Paper.Section2.NormalizationBase
public import SerrePositivity.CommutativeAlgebra.HenselianFinite
public import SerrePositivity.FieldTheory.SeparableBaseChange
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import SerrePositivity.Paper.Section5.Positivity
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Avoidance
public import SerrePositivity.Paper.Section2.LengthAlgebra
public import SerrePositivity.CommutativeAlgebra.GeometricTransitivity
public import SerrePositivity.LengthAlgebra.QuotientBounds
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import SerrePositivity.CommutativeAlgebra.SupportDimension

/-! # 核の場合の設定（論文 §5.1）

## 概要

二つの素イデアル商から補題 2.2 の正規化基底を選び、基底を保ったままガロア閉包へ上げて有限群作用付きの拡大を作る（不変環は基底、剰余体は変わらない）。定理 2.5 で長さ代数を選び、共通剰余体から標数・完全性を、不変環の条件から幾何的推移性を導き、(5.4) のパラメータの選択を経て第一・第二の比較へ接続する。

## 方針

前段（`GaloisNormalizationBasePart`）では、有限で生成点で分離的な整域拡大 `A → D` を分数体拡大の正規閉包の中の `A` の整閉包へ埋め込む。

## 規約

`IsIntegrallyClosed A` は明示的な仮定。この接続に新しい未証明入力はない。

## 使われ方

`Section5/Reduction`。
-/

@[expose] public noncomputable section

universe u v

section GaloisNormalizationPart

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

end GaloisNormalizationPart

section SelectedParameterPositivityPart

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 選んだパラメータ商の代数構造を、正値性の入口と同じ構造として渡す。
/-- 次元条件と `P + Q` の根基からパラメータを選んで、長さ代数による核心の正値性を導く。
正則列、有限拡大上のパラメータ系、`R/(x)` 上の有限代数構造は入力しない。 -/
theorem core_of_lengthAlgebras_with_parameter_choice
    {R D C₀ : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing D] [IsLocalRing D] [CommRing C₀] [Algebra D C₀]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (G₀ : Type u) [Group G₀] [Finite G₀] [MulSemiringAction G₀ D]
    {h : ℕ}
    (hresR : Function.Surjective ((residue D).comp (algebraMap R D)))
    (A₀ : Type u) [CommRing A₀] [IsRegularLocalRing A₀]
    [Algebra A₀ D] [Module.Finite A₀ D] [SMulCommClass G₀ A₀ D]
    (hinj : Function.Injective (algebraMap A₀ D))
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    (t : Fin h → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (p₀ : ℕ) [Fact p₀.Prime]
    [Algebra A₀ C₀] [Algebra (Section2.Tower A₀ t p₀) C₀]
    [IsScalarTower A₀ D C₀] [IsScalarTower A₀ (Section2.Tower A₀ t p₀) C₀]
    (hzeroD : ∀ (z : Fin h → D), IsSystemOfParameters D z →
      ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (koszulHomologySelf (fun j ↦ algebraMap D C₀ (z j ^ v)) q) = 0)
    (hquotD : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (C₀ ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C₀ (z j ^ v))) =
      ENNReal.ofReal ((v : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)))
    (A T C : Type u) [CommRing A] [IsRegularLocalRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
    [Algebra R T] [Algebra (R ⧸ Q) T] [IsScalarTower R (R ⧸ Q) T]
    [Module.Finite (R ⧸ Q) T]
    [CommRing C] [Nontrivial C] [Algebra T C]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G A T]
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    {e : ℕ} (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hdim : ringKrullDim A = e) (hd : ringKrullDim R = (e + h : ℕ))
    (hresA : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hresRT : Function.Surjective ((residue T).comp (algebraMap R T)))
    (hzeroC : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i → lam.len
      (koszulHomologySelf (fun j ↦ algebraMap T C (algebraMap A T (a j) ^ v)) i) = 0)
    (hquotC : ∀ v : ℕ, 0 < v → lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap T C (algebraMap A T (a j) ^ v))) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G)
    (hh : 0 < h) (hdimA₀ : ringKrullDim A₀ = h)
    (hsop : IsSystemOfParameters D (algebraMap A₀ D ∘ t))
    (hsurjD : Function.Surjective (PrimeSpectrum.comap (algebraMap A₀ D)))
    (htransD : IsGeometricallyTransitive A₀ D G₀)
    (rankD : 0 < Module.finrank (R ⧸ P) D) (rankT : 0 < Module.finrank (R ⧸ Q) T)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = e)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (pR : ℕ) [Fact pR.Prime] [CharP (ResidueField R) pR] :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let : FaithfulSMul (R ⧸ P) D := by
    by_contra hn
    exact rankD.ne' (Module.finrank_eq_zero_of_not_faithfulSMul hn)
  obtain ⟨x, hxQ, hreg, hx⟩ := exists_regular_parameters_for_finite_extension P Q D
    (FaithfulSMul.algebraMap_injective (R ⧸ P) D) hd hPdim hQdim hprimary
  have hxQ' : Ideal.span (Set.range x) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hxQ i
  obtain ⟨bAlg, bTower, bFinite⟩ := exists_finite_quotientAlgebra
    (Ideal.span (Set.range x)) Q hxQ' T
  let := bAlg
  have := bTower
  have := bFinite
  exact core_of_lengthAlgebras P Q G₀ x hx hreg hresR A₀ hinj hresD t ht p₀
    hzeroD hquotD A T C G lam a ha hdim hd hresA hresRT hzeroC hquotC p hsurj htrans
    hh hdimA₀ hsop hsurjD htransD rankD rankT hPdim hQdim hprimary pR

end SerrePositivity.Section5

end SelectedParameterPositivityPart

section NormalizationPositivityPart

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 二つの存在定理が返す代数構造を同時に保持して、正値性の入口へ渡す。
/-- 正規化基底と不変環の条件から核心の交点数は正。
長さ代数、その公式、パラメータ、正の階数、幾何的推移性は内部で供給する。
有限拡大・正規化基底・有限群作用の存在構成は、この定理の前段に残る。 -/
theorem core_of_normalization_bases
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [PerfectField (ResidueField R)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    {h e : ℕ} (hh : 0 < h) (he : 0 < e)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = e)
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (D T : Type u) [CommRing D] [IsLocalRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (hinjPD : Function.Injective (algebraMap (R ⧸ P) D))
    (hresRD : Function.Surjective ((residue D).comp (algebraMap R D)))
    [CommRing T] [IsLocalRing T] [IsDomain T] [IsAdicComplete (maximalIdeal T) T]
    [Algebra R T] [Algebra (R ⧸ Q) T] [IsScalarTower R (R ⧸ Q) T]
    [Module.Finite (R ⧸ Q) T] (hinjQT : Function.Injective (algebraMap (R ⧸ Q) T))
    (hresRT : Function.Surjective ((residue T).comp (algebraMap R T)))
    (A₀ A : Type u) [CommRing A₀] [IsRegularLocalRing A₀]
    [IsAdicComplete (maximalIdeal A₀) A₀]
    [Algebra A₀ D] [Module.Finite A₀ D]
    (hinjD : Function.Injective (algebraMap A₀ D))
    (hsepD : ∀ d : D, ((minpoly A₀ d).map (algebraMap A₀ (FractionRing A₀))).Separable)
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    (t : Fin h → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (hdimA₀ : ringKrullDim A₀ = h)
    [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [Algebra A T] [Module.Finite A T]
    (hinjT : Function.Injective (algebraMap A T))
    (hsepT : ∀ d : T, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))
    (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hdimA : ringKrullDim A = e)
    (G₀ G : Type u) [Group G₀] [Finite G₀] [MulSemiringAction G₀ D]
    [SMulCommClass G₀ A₀ D] [Group G] [Finite G] [MulSemiringAction G T]
    [SMulCommClass G A T]
    (hfixD : ∀ d : D, (∀ g : G₀, g • d = d) → d ∈ Set.range (algebraMap A₀ D))
    (hfixT : ∀ d : T, (∀ g : G, g • d = d) → d ∈ Set.range (algebraMap A T))
    (hbaseD :
      (CharP D p ∧ ∃ f : A₀ ≃+* MvPowerSeries (Fin h) (ResidueField D),
        ∀ i, f (t i) = MvPowerSeries.X i) ∨
      (CharZero D ∧ t ⟨0, hh⟩ = (p : A₀) ∧
        ∃ f : A₀ ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0}
          (WittVector p (ResidueField D)),
          ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), f (t i) = MvPowerSeries.X ⟨i, hi⟩))
    (hbaseT :
      (CharP T p ∧ ∃ f : A ≃+* MvPowerSeries (Fin e) (ResidueField T),
        ∀ i, f (a i) = MvPowerSeries.X i) ∨
      (CharZero T ∧ a ⟨0, he⟩ = (p : A) ∧
        ∃ f : A ≃+* MvPowerSeries {i : Fin e // (i : ℕ) ≠ 0}
          (WittVector p (ResidueField T)),
          ∀ (i : Fin e) (hi : (i : ℕ) ≠ 0), f (a i) = MvPowerSeries.X ⟨i, hi⟩)) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  have : IsNoetherianRing D := IsNoetherianRing.of_finite A₀ D
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  let eD := residueFieldEquiv_of_surjective D hresRD
  let eT := residueFieldEquiv_of_surjective T hresRT
  let eA := residueFieldEquiv_of_surjective T hresT
  have : CharP (ResidueField D) p :=
    charP_of_injective_ringHom (f := eD.toRingHom) eD.injective p
  have : CharP (ResidueField T) p :=
    charP_of_injective_ringHom (f := eT.toRingHom) eT.injective p
  have : CharP (ResidueField A) p :=
    charP_of_injective_ringHom (f := eA.symm.toRingHom) eA.symm.injective p
  have : PerfectField (ResidueField D) := PerfectField.of_ringEquiv eD
  have : PerfectField (ResidueField T) := PerfectField.of_ringEquiv eT
  have htSop : IsSystemOfParameters A₀ t :=
    ⟨hdimA₀, by rw [ht]; exact (maximalIdeal.isMaximal A₀).isPrime.radical⟩
  have haSop : IsSystemOfParameters A a :=
    ⟨hdimA, by rw [ha]; exact (maximalIdeal.isMaximal A).isPrime.radical⟩
  have htD := htSop.map_finite D hinjD
  have haT := haSop.map_finite T hinjT
  obtain ⟨C₀, c₀Ring, a₀Alg, dAlg, t₀Alg, ad₀Tower, at₀Tower, hzeroD, hquotD, _⟩ :=
    Section2.theorem_2_5 A₀ D hinjD hsepD hresD t hdimA₀ htD.1 hh ht htD p hbaseD
  obtain ⟨C, cRing, aAlg, tAlg, towerAlg, atTower, aTower, hzeroT, _, hquotT⟩ :=
    Section2.theorem_2_5 A T hinjT hsepT hresT a hdimA haT.1 he ha haT p hbaseT
  let lam := Section2.towerLengthOn A T hinjT a p
    (fun i ↦ ha ▸ Ideal.subset_span (Set.mem_range_self i)) C
  have : Module.IsTorsionFree (R ⧸ P) D :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjPD
  have : Module.IsTorsionFree (R ⧸ Q) T :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjQT
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  have : Module.IsTorsionFree A T := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjT
  have hrank : 0 < Module.finrank A T := Module.finrank_pos
  have hpos : 0 < lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap T C (algebraMap A T (a j) ^ 1))) := by
    rw [hquotT 1 one_pos]
    simpa only [one_pow, one_mul] using
      (show (0 : ℝ≥0∞) < (Module.finrank A T : ℝ≥0∞) by exact_mod_cast hrank)
  have : Nontrivial C := lam.nontrivial_ring_of_len_pos _ hpos
  let : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  have : FaithfulSMul A₀ D := (faithfulSMul_iff_algebraMap_injective A₀ D).mpr hinjD
  have : FaithfulSMul A T := (faithfulSMul_iff_algebraMap_injective A T).mpr hinjT
  have hd : ringKrullDim R = (e + h : ℕ) := by
    rw [← hsum, hPdim, hQdim, Nat.cast_add, add_comm]
  exact core_of_lengthAlgebras_with_parameter_choice P Q G₀ hresRD A₀ hinjD hresD t ht p
    hzeroD hquotD A T C G lam a ha hdimA hd hresT hresRT (hzeroT _ haT) hquotT p
    (Algebra.IsIntegral.comap_surjective A T) (isGeometricallyTransitive_of_fixed hfixT)
    hh hdimA₀ htD (Algebra.IsIntegral.comap_surjective A₀ D)
    (isGeometricallyTransitive_of_fixed hfixD) Module.finrank_pos Module.finrank_pos
    hPdim hQdim hprimary p

end SerrePositivity.Section5

end NormalizationPositivityPart

section CorePart

namespace SerrePositivity.Section5

open IsLocalRing

set_option synthInstance.maxSize 2048

/-- 正次元の素イデアル商が固有に交わる核心の場合の正値性。
正規化基底、有限拡大、群作用の選択はすべてこの証明の内部で行う。 -/
theorem core_of_complete_algClosed
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : 0 < ringKrullDim (R ⧸ P)) (hQ : 0 < ringKrullDim (R ⧸ Q))
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) :=
    isAdicComplete_finite_local_algebra (R := R) (R ⧸ P)
  let : IsAdicComplete (maximalIdeal (R ⧸ Q)) (R ⧸ Q) :=
    isAdicComplete_finite_local_algebra (R := R) (R ⧸ Q)
  let eP := residueFieldEquiv_of_surjective (R ⧸ P)
    (residue_surjective_of_finite_of_isAlgClosed R (R ⧸ P))
  let eQ := residueFieldEquiv_of_surjective (R ⧸ Q)
    (residue_surjective_of_finite_of_isAlgClosed R (R ⧸ Q))
  let : IsAlgClosed (ResidueField (R ⧸ P)) := IsAlgClosed.of_ringEquiv _ _ eP
  let : IsAlgClosed (ResidueField (R ⧸ Q)) := IsAlgClosed.of_ringEquiv _ _ eQ
  let : CharP (ResidueField (R ⧸ P)) p :=
    charP_of_injective_ringHom (f := eP.toRingHom) eP.injective p
  let : CharP (ResidueField (R ⧸ Q)) p :=
    charP_of_injective_ringHom (f := eQ.toRingHom) eQ.injective p
  obtain ⟨h, hPdim⟩ := exists_nat_ringKrullDim_eq (R ⧸ P)
  obtain ⟨e, hQdim⟩ := exists_nat_ringKrullDim_eq (R ⧸ Q)
  have hh : 0 < h := by exact_mod_cast (hPdim ▸ hP)
  have he : 0 < e := by exact_mod_cast (hQdim ▸ hQ)
  obtain ⟨A₀, D, a₀Ring, a₀Reg, a₀Complete, dRing, dDomain, dLocal, dComplete,
      a₀dAlg, pdAlg, hA₀D, hPD, hinjD, hinjPD, hresD, _, hsepD, hG₀, hfixD,
      hdimA₀, t, ht, hbaseD⟩ := exists_regular_galoisNormalization (R ⧸ P) hPdim hh p
  obtain ⟨A, T, aRing, aReg, aComplete, tRing, tDomain, tLocal, tComplete,
      atAlg, qtAlg, hAT, hQT, hinjT, hinjQT, hresT, _, hsepT, hG, hfixT,
      hdimA, a, ha, hbaseT⟩ := exists_regular_galoisNormalization (R ⧸ Q) hQdim he p
  let := hA₀D
  let := hPD
  let := hAT
  let := hQT
  let := hG₀
  let := hG
  let : Algebra R D := ((algebraMap (R ⧸ P) D).comp (algebraMap R (R ⧸ P))).toAlgebra
  let : IsScalarTower R (R ⧸ P) D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R D := Module.Finite.trans (R ⧸ P) D
  let : Algebra R T := ((algebraMap (R ⧸ Q) T).comp (algebraMap R (R ⧸ Q))).toAlgebra
  let : IsScalarTower R (R ⧸ Q) T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R T := Module.Finite.trans (R ⧸ Q) T
  exact core_of_normalization_bases p P Q hh he hPdim hQdim hsum hprimary
    D T hinjPD (residue_surjective_of_finite_of_isAlgClosed R D)
    hinjQT (residue_surjective_of_finite_of_isAlgClosed R T)
    A₀ A hinjD hsepD hresD t ht hdimA₀ hinjT hsepT hresT a ha hdimA
    (D ≃ₐ[A₀] D) (T ≃ₐ[A] T) hfixD hfixT hbaseD hbaseT

end SerrePositivity.Section5

end CorePart
