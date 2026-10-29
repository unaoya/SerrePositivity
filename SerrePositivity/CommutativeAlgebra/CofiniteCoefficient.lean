module

public import SerrePositivity.FieldTheory.PBasisCofiniteField
public import SerrePositivity.CommutativeAlgebra.CompletedDifferential
public import SerrePositivity.RingTheory.Kaehler
public import SerrePositivity.FieldTheory.PBasisDifferentials
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Equalizer
public import SerrePositivity.RingTheory.Derivation

/-! # 中間係数体上の微分

概要：体 `K` の p 基底 `b` と有限集合 `e` について、中間係数体 `K_e`（`pBasisCofiniteField`）上の微分を扱う。
- `S` が完備 Noether 局所で `K → S` が剰余体へ全射なら、準素イデアル `I` に沿う `Ω̂_{S/K_e}` は有限で、
  極大イデアル進のものは生成点で普遍微分の像に張られる。
- 係数写像 `φ : K → S` に沿う `Ω_{S/K_e}` は、絶対微分 `Ω_{S/ℤ}` を `e` の外の `D(φ b_j)` で割ったもの。
  したがって `e` の外で一致する二つの係数写像の上の微分（とその完備化・係数拡大）は自然に同型。
- `K_e → K` に沿う係数制限の核は、残した方向 `b_i`（`i ∈ e`）の微分で張られる（完備化しても同じ）。
方針：`K/K_e` は有限（`IsPBasis.finite_cofiniteField`）なので、閉ファイバーの有限性と完備微分の一般論
（`CompletedDifferential`）がそのまま使える。核は、`K_e` が `K^p` に `e` の外の `b_j` を添加した体であることと、
`p` 乗の微分が零であること（`derivationOverPowers`）から。
規約：係数写像 `φ` は型 `cofiniteCoefficientDifferential e φ` に保持し、文脈の別の `K` 作用と混同しない。
使われ方：Cohen–Gabber の係数切断の取り替え（`PBasisIndependentCoefficientPerturbation`・
`CohenGabberCoefficientField`）、固定した正規化での次元計算（`CofiniteNormalization`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Finite

universe u
open IsLocalRing


/-- 共通剰余体を持つ準素商の有限性を、中間係数体へ制限する。 -/
theorem IsPBasis.moduleFinite_primaryQuotient_cofiniteField
    {K S : Type u} [Field K] [CommRing S] [Algebra K S]
    [IsNoetherianRing S] [IsLocalRing S]
    {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue S).comp (algebraMap K S)))
    (I : Ideal S) (hI : I.radical = maximalIdeal S) :
    Module.Finite (pBasisCofiniteField (p := p) b e) (S ⧸ I) := by
  let E := pBasisCofiniteField (p := p) b e
  let : Module.Finite E K := hb.finite_cofiniteField e
  let : Module.Finite K (S ⧸ I) := finite_quotient_of_common_residue_primary hres I hI
  exact Module.Finite.trans K _

/-- 準素なパラメータの閉ファイバーは各中間係数体上でも有限。
従って、その係数体上の完備微分も有限生成。 -/
theorem IsPBasis.moduleFinite_completedKaehler_cofiniteField
    {K S : Type u} [Field K] [CommRing S] [Algebra K S]
    [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue S).comp (algebraMap K S)))
    (I : Ideal S) (hI : I.radical = maximalIdeal S) :
    Module.Finite S (AdicCompletion I
      (KaehlerDifferential (pBasisCofiniteField (p := p) b e) S)) := by
  let E := pBasisCofiniteField (p := p) b e
  let : Module.Finite E (S ⧸ I) := hb.moduleFinite_primaryQuotient_cofiniteField e hres I hI
  have hIm : I ≤ maximalIdeal S := by rw [← hI]; exact Ideal.le_radical
  let : IsAdicComplete I S := isAdicComplete_finite_of_le_maximalIdeal I hIm
  exact moduleFinite_completedKaehler_of_finiteType_fiber I I.fg_of_isNoetherianRing

end Finite

section Restriction

variable {K S ι : Type*} [Field K] [CommRing S]
  {p : ℕ} [Fact p.Prime] [CharP K p] {b : ι → K}
  (e : Finset ι)
local notation "E" => pBasisCofiniteField (p := p) b e

/-- 指定した係数写像によるκ_e作用を型に保持した通常微分。 -/
abbrev cofiniteCoefficientDifferential (φ : K →+* S) :=
  letI : Algebra K S := φ.toAlgebra
  KaehlerDifferential E S

/-- S上の加群作用は、型に保持した係数写像で構成する。
別のK作用が文脈にある場合にも、そちらの微分加群の作用を選ばない。 -/
instance cofiniteCoefficientDifferentialModule (φ : K →+* S) :
    Module S (cofiniteCoefficientDifferential (b := b) e φ) := by
  let : Algebra K S := φ.toAlgebra
  infer_instance

/-- 指定した係数写像に沿う、絶対微分からの通常の係数制限。 -/
def cofiniteKaehlerRestriction (φ : K →+* S) :
    letI : Algebra K S := φ.toAlgebra
    KaehlerDifferential ℤ S →ₗ[S] KaehlerDifferential E S := by
  let : Algebra K S := φ.toAlgebra
  exact KaehlerDifferential.map ℤ E S S

@[simp] theorem cofiniteKaehlerRestriction_D (φ : K →+* S) (s : S) :
    letI : Algebra K S := φ.toAlgebra
    cofiniteKaehlerRestriction (b := b) e φ (KaehlerDifferential.D ℤ S s) =
      KaehlerDifferential.D E S s := by
  let : Algebra K S := φ.toAlgebra
  exact KaehlerDifferential.map_D ℤ E S S s

/-- 絶対微分からκ_e上への係数制限の核は、eの外の指定係数の微分の線形包。 -/
theorem IsPBasis.ker_cofiniteKaehlerRestriction (hb : IsPBasis K p b) (φ : K →+* S) :
    letI : Algebra K S := φ.toAlgebra
    LinearMap.ker (cofiniteKaehlerRestriction (b := b) e φ) =
      Submodule.span S (Set.range (fun j : {i : ι // i ∉ e} ↦
        KaehlerDifferential.D ℤ S (φ (b j)))) := by
  let : Algebra K S := φ.toAlgebra
  rw [cofiniteKaehlerRestriction, ker_kaehlerRestriction_eq_span]
  let c : {i : ι // i ∉ e} → E := fun j ↦ ⟨b j, mem_pBasisCofiniteField b e j.property⟩
  have hadjoin : Algebra.adjoin (pPowerSubfield K p) (Set.range c) = ⊤ := by
    apply adjoin_eq_top_of_pMonomialBasis (hb.cofiniteCoefficientBasis e)
    intro d
    apply Subtype.ext
    rw [hb.cofiniteCoefficientBasis_apply_coe]
    change pMonomial (fun j : {i : ι // i ∉ e} ↦ b j) d = algebraMap E K (pMonomial c d)
    simp only [pMonomial, map_finsuppProd, map_pow]
    rfl
  let δ : Derivation (pPowerSubfield K p) E (KaehlerDifferential ℤ S) :=
    (derivationOverPowers (p := p) ((KaehlerDifferential.D ℤ S).compAlgebraMap K)).compAlgebraMap E
  have hspan := span_range_derivation_eq_span_of_adjoin_eq_top δ (Set.range c) hadjoin
  rw [← Set.range_comp] at hspan
  have h := congrArg (fun P : Submodule E (KaehlerDifferential ℤ S) ↦
    Submodule.span S (P : Set (KaehlerDifferential ℤ S))) hspan
  simp only [Submodule.span_span_of_tower] at h
  exact h

/-- 残す方向の外で係数写像が一致すると、絶対微分からの二つの係数制限の核は一致。 -/
theorem IsPBasis.ker_cofiniteKaehlerRestriction_eq (hb : IsPBasis K p b)
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) :
    LinearMap.ker (cofiniteKaehlerRestriction (b := b) e φ) =
      LinearMap.ker (cofiniteKaehlerRestriction (b := b) e ψ) := by
  rw [hb.ker_cofiniteKaehlerRestriction e φ, hb.ker_cofiniteKaehlerRestriction e ψ]
  have hfn : (fun j : {i : ι // i ∉ e} ↦ KaehlerDifferential.D ℤ S (φ (b j))) =
      (fun j : {i : ι // i ∉ e} ↦ KaehlerDifferential.D ℤ S (ψ (b j))) := by
    funext j
    rw [hagree j j.property]
  rw [hfn]

/-- 異なる係数作用を保持して、共通の絶対微分の商を通じて通常微分を比較する。 -/
def IsPBasis.cofiniteCoefficientDifferentialEquiv (hb : IsPBasis K p b)
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) :
    cofiniteCoefficientDifferential (b := b) e φ ≃ₗ[S]
      cofiniteCoefficientDifferential (b := b) e ψ :=
  ((cofiniteKaehlerRestriction e φ).quotKerEquivOfSurjective
    (by let : Algebra K S := φ.toAlgebra
        exact KaehlerDifferential.map_surjective ℤ E S)).symm |>.trans
    ((Submodule.quotEquivOfEq _ _ (hb.ker_cofiniteKaehlerRestriction_eq e φ ψ hagree)).trans
      ((cofiniteKaehlerRestriction e ψ).quotKerEquivOfSurjective
        (by let : Algebra K S := ψ.toAlgebra; exact KaehlerDifferential.map_surjective ℤ E S)))

/-- 比較は同じ絶対普遍微分の像を保つ。 -/
theorem IsPBasis.cofiniteCoefficientDifferentialEquiv_restriction
    (hb : IsPBasis K p b) (φ ψ : K →+* S)
    (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) (ω : KaehlerDifferential ℤ S) :
    hb.cofiniteCoefficientDifferentialEquiv e φ ψ hagree (cofiniteKaehlerRestriction e φ ω) =
      cofiniteKaehlerRestriction e ψ ω := by
  simp [IsPBasis.cofiniteCoefficientDifferentialEquiv]

/-- 完備化もMathlibの関手性で比較する。根基・有限性・Noether性は不要。 -/
def IsPBasis.cofiniteCoefficientCompletedDifferentialEquiv (hb : IsPBasis K p b)
    (I : Ideal S) (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) :
    AdicCompletion I (cofiniteCoefficientDifferential (b := b) e φ) ≃ₗ[S]
      AdicCompletion I (cofiniteCoefficientDifferential (b := b) e ψ) :=
  (AdicCompletion.congr I (hb.cofiniteCoefficientDifferentialEquiv e φ ψ hagree)).restrictScalars S

@[simp] theorem IsPBasis.cofiniteCoefficientCompletedDifferentialEquiv_of_restriction
    (hb : IsPBasis K p b) (I : Ideal S) (φ ψ : K →+* S)
    (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) (ω : KaehlerDifferential ℤ S) :
    hb.cofiniteCoefficientCompletedDifferentialEquiv e I φ ψ hagree
      (AdicCompletion.of I _ (cofiniteKaehlerRestriction e φ ω)) =
        AdicCompletion.of I _ (cofiniteKaehlerRestriction e ψ ω) := by
  change AdicCompletion.map I (hb.cofiniteCoefficientDifferentialEquiv e φ ψ hagree).toLinearMap
    (AdicCompletion.of I _ (cofiniteKaehlerRestriction e φ ω)) = _
  rw [AdicCompletion.map_of]
  exact congrArg (AdicCompletion.of I _) (hb.cofiniteCoefficientDifferentialEquiv_restriction
    e φ ψ hagree ω)

/-- 同じS上の係数拡大を施しても、異なる係数写像の完備微分を比較できる。 -/
def IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv
    (hb : IsPBasis K p b) (I : Ideal S) (L : Type*) [CommRing L] [Algebra S L]
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) :
    TensorProduct S L (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e φ)) ≃ₗ[L]
      TensorProduct S L (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e ψ)) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
    (hb.cofiniteCoefficientCompletedDifferentialEquiv e I φ ψ hagree)

@[simp] theorem IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_tmul_of
    (hb : IsPBasis K p b) (I : Ideal S) (L : Type*) [CommRing L] [Algebra S L]
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i))
    (l : L) (ω : KaehlerDifferential ℤ S) :
    hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv e I L φ ψ hagree
      (TensorProduct.tmul S l (AdicCompletion.of I _ (cofiniteKaehlerRestriction e φ ω))) =
        TensorProduct.tmul S l (AdicCompletion.of I _ (cofiniteKaehlerRestriction e ψ ω)) := by
  simp [IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv]

/-- 生成点での次元は、補集合のp-basisの像を保つ係数変更で保存される。 -/
theorem IsPBasis.finrank_cofiniteCoefficientBaseChangeCompletedDifferential
    (hb : IsPBasis K p b) (I : Ideal S) (L : Type*) [Field L] [Algebra S L]
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) :
    Module.finrank L (TensorProduct S L
      (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e φ))) =
    Module.finrank L (TensorProduct S L
      (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e ψ))) :=
  (hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv e I L φ ψ hagree).finrank_eq

end Restriction

section Generation

universe u
open IsLocalRing
open scoped TensorProduct
variable {K D : Type u} [Field K] [CommRing D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}

/-- 共有限係数体上の完備微分の生成点は有限次元。 -/
theorem IsPBasis.moduleFinite_baseChange_completedKaehler_cofiniteField
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue D).comp (algebraMap K D))) :
    Module.Finite (FractionRing D) (FractionRing D ⊗[D]
      AdicCompletion (maximalIdeal D)
        (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) := by
  let : Module.Finite D (AdicCompletion (maximalIdeal D)
      (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) :=
    hb.moduleFinite_completedKaehler_cofiniteField e hres (maximalIdeal D)
      (maximalIdeal.isMaximal D).isPrime.radical
  infer_instance

/-- 共有限係数体上の完備微分の生成点は普遍微分の像で生成される。 -/
theorem IsPBasis.span_range_baseChange_completedKaehler_cofiniteField
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue D).comp (algebraMap K D))) :
    Submodule.span (FractionRing D) (Set.range
      (baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D))) = ⊤ := by
  let : Module.Finite D (AdicCompletion (maximalIdeal D)
      (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) :=
    hb.moduleFinite_completedKaehler_cofiniteField e hres (maximalIdeal D)
      (maximalIdeal.isMaximal D).isPrime.radical
  exact span_range_baseChangeCompletedKaehlerDerivation_eq_top (FractionRing D)
    (maximalIdeal D) (maximalIdeal_le_jacobson ⊥)

end Generation

section FullRestriction

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}

/-- 中間係数体から全係数体への通常微分の核は、残した有限係数方向の微分。 -/
theorem IsPBasis.ker_cofiniteToFullKaehlerRestriction
    (hb : IsPBasis K p b) (e : Finset ι) :
    LinearMap.ker (KaehlerDifferential.map (pBasisCofiniteField (p := p) b e) K S S) =
      Submodule.span S (Set.range (fun i : e ↦
        KaehlerDifferential.D (pBasisCofiniteField (p := p) b e) S (algebraMap K S (b i)))) := by
  let E := pBasisCofiniteField (p := p) b e
  rw [ker_kaehlerRestriction_eq_span E K S]
  let δ := (KaehlerDifferential.D E S).compAlgebraMap K
  have h := congrArg (fun P : Submodule K (KaehlerDifferential E S) ↦
    Submodule.span S (P : Set (KaehlerDifferential E S)))
    (span_range_derivation_eq_span_of_adjoin_eq_top δ
      (Set.range (fun i : e ↦ b i)) (hb.adjoin_cofiniteField_eq_top e))
  simp only [Submodule.span_span_of_tower, ← Set.range_comp] at h
  exact h

/-- 有限な完備中項の係数制限の核も、残した有限係数方向で生成される。 -/
theorem IsPBasis.ker_completed_cofiniteToFullKaehlerRestriction
    (hb : IsPBasis K p b) (e : Finset ι) [IsNoetherianRing S]
    (I : Ideal S) (hI : I ≤ Ideal.jacobson (⊥ : Ideal S))
    [Module.Finite S (AdicCompletion I
      (KaehlerDifferential (pBasisCofiniteField (p := p) b e) S))] :
    LinearMap.ker ((AdicCompletion.map I
      (KaehlerDifferential.map (pBasisCofiniteField (p := p) b e) K S S)).restrictScalars S) =
      Submodule.span S (Set.range (fun i : e ↦
        AdicCompletion.of I _
          (KaehlerDifferential.D (pBasisCofiniteField (p := p) b e) S (algebraMap K S (b i))))) :=
  ker_adicCompletion_map_eq_span_of_ker_eq_span I hI _
    (KaehlerDifferential.map_surjective _ K S)
    _ (hb.ker_cofiniteToFullKaehlerRestriction e)

end FullRestriction

end SerrePositivity
