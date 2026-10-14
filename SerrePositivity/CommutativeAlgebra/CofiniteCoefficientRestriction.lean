module

public import SerrePositivity.CommutativeAlgebra.KaehlerRestrictionKernel
public import SerrePositivity.FieldTheory.PBasisCofiniteBasis
public import SerrePositivity.FieldTheory.RelativePBasisDifferentials
public import SerrePositivity.FieldTheory.PBasisDifferentials
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 中間係数体上の微分の共通商表示

指定された係数写像κ→Sに沿うκ_e上の微分を、絶対微分の商として比較する。
p乗係数の微分は零なので、核はeの外のp-basis元の微分だけで生成される。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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

/-- 共通の絶対微分の商から、指定した係数写像上の相対微分への自然な同型。 -/
def IsPBasis.cofiniteCoefficientQuotientEquiv (hb : IsPBasis K p b) (φ : K →+* S) :
    (KaehlerDifferential ℤ S ⧸ Submodule.span S
      (Set.range (fun j : {i : ι // i ∉ e} ↦ KaehlerDifferential.D ℤ S (φ (b j))))) ≃ₗ[S]
        cofiniteCoefficientDifferential (b := b) e φ := by
  let : Algebra K S := φ.toAlgebra
  exact (Submodule.quotEquivOfEq _ _ (hb.ker_cofiniteKaehlerRestriction e φ).symm).trans
    ((cofiniteKaehlerRestriction e φ).quotKerEquivOfSurjective
      (KaehlerDifferential.map_surjective ℤ E S))

@[simp] theorem IsPBasis.cofiniteCoefficientQuotientEquiv_mk_D
    (hb : IsPBasis K p b) (φ : K →+* S) (s : S) :
    letI : Algebra K S := φ.toAlgebra
    hb.cofiniteCoefficientQuotientEquiv e φ
      (Submodule.Quotient.mk (KaehlerDifferential.D ℤ S s)) =
        KaehlerDifferential.D E S s := by
  let : Algebra K S := φ.toAlgebra
  simp only [IsPBasis.cofiniteCoefficientQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  exact cofiniteKaehlerRestriction_D e φ s

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

/-- 生成点での有限性も同型に沿って新しい係数作用へ移す。 -/
theorem IsPBasis.moduleFinite_cofiniteCoefficientBaseChangeCompletedDifferential
    (hb : IsPBasis K p b) (I : Ideal S) (L : Type*) [CommRing L] [Algebra S L]
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i))
    [Module.Finite L (TensorProduct S L
      (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e φ)))] :
    Module.Finite L (TensorProduct S L
      (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e ψ))) :=
  Module.Finite.equiv (hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv e I L φ ψ hagree)

/-- 生成点での次元は、補集合のp-basisの像を保つ係数変更で保存される。 -/
theorem IsPBasis.finrank_cofiniteCoefficientBaseChangeCompletedDifferential
    (hb : IsPBasis K p b) (I : Ideal S) (L : Type*) [Field L] [Algebra S L]
    (φ ψ : K →+* S) (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) :
    Module.finrank L (TensorProduct S L
      (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e φ))) =
    Module.finrank L (TensorProduct S L
      (AdicCompletion I (cofiniteCoefficientDifferential (b := b) e ψ))) :=
  (hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv e I L φ ψ hagree).finrank_eq

end SerrePositivity
