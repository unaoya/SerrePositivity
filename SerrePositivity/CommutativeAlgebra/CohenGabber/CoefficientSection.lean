module

public import SerrePositivity.CommutativeAlgebra.CoefficientField
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficient
public import SerrePositivity.CommutativeAlgebra.CofiniteNormalization
public import SerrePositivity.RingTheory.Derivation
public import Mathlib.RingTheory.Localization.Module

/-! # Cohen–Gabber 1：係数切断の取り替えと完備微分の次元

概要：同標数 `p` の次元 `h` の完備 Noether 局所整域 `D` と係数切断 `φ : k = D/m → D` を考える（`m ≠ 0`）。
係数切断を取り替えて `ψ` とすると、`ψ` に沿う完備微分の生成点での次元が `h` になる
（`IsPBasis.exists_coefficient_section_completed_finrank`）。
方針：
1. 中間係数体 `K_e` 上の完備微分の生成点での次元は、十分大きな `e` で `h + |e|`（`CofiniteNormalization`）。
2. 普遍微分の像は生成点で全体を張る（`CofiniteCoefficient`）ので、極大イデアルの元 `μ_i` を選んで
   `D(φ(b_i) + μ_i)`（`i ∈ e`）を独立にできる（`exists_linearIndependent_derivation_perturbation`）。
3. `b_i ↦ φ(b_i) + μ_i`（`i ∈ e`）、それ以外は `φ` と同じ値となる係数切断 `ψ` を、p 基底の持ち上げ（`CoefficientField`）で作る。
   `e` の外で一致するので、`K_e` 上の完備微分は `φ` と `ψ` で同型（`CofiniteCoefficient`）。
4. `Ω̂_{D/K_e} → Ω̂_{D/k}` は全射で、核は残した方向の微分が張る。これが独立なので次元が `|e|` 下がって `h`。
規約：係数切断は型 `cofiniteCoefficientDifferential e ψ` に保持し、異なる係数作用を混同しない。
使われ方：微分パラメータの選択（`CohenGabber/Parameters`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Perturbation

variable {K S ι : Type*} [Field K] [CommRing S]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP S p] {b : ι → K}

/-- 核について完備な全射の切断を、有限個の指定p-basis方向だけ摂動する。 -/
theorem IsPBasis.exists_section_of_finitePerturbation (hb : IsPBasis K p b)
    (f : S →+* K) (hf : Function.Surjective f) [IsAdicComplete (RingHom.ker f) S]
    (φ : K →+* S) (hφ : f.comp φ = RingHom.id K)
    (e : Finset ι) (μ : e → RingHom.ker f) :
    ∃ ψ : K →+* S, f.comp ψ = RingHom.id K ∧
      (∀ j : e, ψ (b j) = φ (b j) + μ j) ∧
        ∀ i, i ∉ e → ψ (b i) = φ (b i) := by
  classical
  let β : ι → S := fun i ↦ if hi : i ∈ e then φ (b i) + μ ⟨i, hi⟩ else φ (b i)
  have hβ : ∀ i, f (β i) = b i := by
    intro i
    have hi : f (φ (b i)) = b i := RingHom.congr_fun hφ (b i)
    dsimp [β]
    split_ifs with hie
    · rw [map_add, RingHom.mem_ker.mp (μ ⟨i, hie⟩).property, add_zero, hi]
    · exact hi
  obtain ⟨ψ, hψ, _⟩ := hb.existsUnique_ringHom_lift_of_complete_kernel f hf β hβ
  refine ⟨ψ, hψ.1, ?_, ?_⟩
  · intro j
    simpa [β, j.property] using hψ.2 j
  · intro i hi
    simpa [β, hi] using hψ.2 i

end Perturbation

universe u
open scoped TensorProduct
open IsLocalRing

section Independent


section ExplicitCoefficient
variable {K S L ι : Type*} [Field K] [CommRing S] [CommRing L] [Algebra S L]
  {p : ℕ} [Fact p.Prime] [CharP K p] {b : ι → K}

/-- 指定係数写像に沿う共有限完備微分への絶対導分。 -/
def cofiniteCoefficientBaseChangeCompletedDerivation (e : Finset ι) (I : Ideal S)
    (φ : K →+* S) :
    Derivation ℤ S (L ⊗[S] AdicCompletion I
      (cofiniteCoefficientDifferential (p := p) (b := b) e φ)) :=
  ((TensorProduct.mk S L _ 1).comp
    ((AdicCompletion.of I _).comp (cofiniteKaehlerRestriction (b := b) e φ))).compDer
      (KaehlerDifferential.D ℤ S)

@[simp] theorem cofiniteCoefficientBaseChangeCompletedDerivation_apply
    (e : Finset ι) (I : Ideal S) (φ : K →+* S) (s : S) :
    cofiniteCoefficientBaseChangeCompletedDerivation (L := L) (b := b) e I φ s =
      1 ⊗ₜ[S] AdicCompletion.of I _
        (cofiniteKaehlerRestriction (b := b) e φ (KaehlerDifferential.D ℤ S s)) := rfl

/-- 共通商による比較は指定係数の導分を保つ。 -/
@[simp] theorem IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_derivation
    (hb : IsPBasis K p b) (e : Finset ι) (I : Ideal S) (φ ψ : K →+* S)
    (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) (s : S) :
    hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv e I L φ ψ hagree
      (cofiniteCoefficientBaseChangeCompletedDerivation (L := L) (b := b) e I φ s) =
        cofiniteCoefficientBaseChangeCompletedDerivation (L := L) (b := b) e I ψ s :=
  hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_tmul_of
    e I L φ ψ hagree 1 (KaehlerDifferential.D ℤ S s)
end ExplicitCoefficient

section Selection
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}

/-- 通常の有限正規化の次元計算から、有限係数方向を独立にする極大イデアル内の元を選ぶ。 -/
theorem IsPBasis.exists_independent_coefficient_perturbation
    (hb : IsPBasis K p b) {h : ℕ} (hdim : ringKrullDim D = h)
    (hres : Function.Surjective ((residue D).comp (algebraMap K D)))
    (hm : maximalIdeal D ≠ ⊥)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ e : Finset ι, ∃ μ : e → D, (∀ i, μ i ∈ maximalIdeal D) ∧
      LinearIndependent (FractionRing D) (fun i : e ↦
        baseChangeCompletedKaehlerDerivation
          (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D)
            (algebraMap K D (b i) + μ i)) ∧
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) = h + e.card := by
  classical
  obtain ⟨e, he⟩ := hb.exists_completed_finrank_of_parameters hdim hres z hzm hprimary
  let E := pBasisCofiniteField (p := p) b e
  let V := FractionRing D ⊗[D] AdicCompletion (maximalIdeal D) (KaehlerDifferential E D)
  let : Module.Finite (FractionRing D) V :=
    hb.moduleFinite_baseChange_completedKaehler_cofiniteField e hres
  let δ := baseChangeCompletedKaehlerDerivation (k := E) (FractionRing D) (maximalIdeal D)
  obtain ⟨μ, hμ, hi⟩ := exists_linearIndependent_derivation_perturbation
    δ (maximalIdeal D) hm (hb.span_range_baseChange_completedKaehler_cofiniteField e hres)
    (fun i : e ↦ δ (algebraMap K D (b i))) (by
      rw [he e (Finset.Subset.refl e), Fintype.card_coe]
      omega)
  exact ⟨e, μ, hμ, (by simpa only [map_add] using hi), he e (Finset.Subset.refl e)⟩
end Selection

section ResidueSection
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP D p] [CharP (ResidueField D) p]
  {ι : Type*} {b : ι → ResidueField D}

/-- 極大イデアルが非零なら、微分独立な有限係数方向を持つ新しい係数切断を構成する。 -/
theorem IsPBasis.exists_independent_coefficient_section
    (hb : IsPBasis (ResidueField D) p b)
    (φ : ResidueField D →+* D) (hφ : (residue D).comp φ = RingHom.id (ResidueField D))
    {h : ℕ} (hdim : ringKrullDim D = h) (hm : maximalIdeal D ≠ ⊥)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ (e : Finset ι) (ψ : ResidueField D →+* D),
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      (∀ i, i ∉ e → φ (b i) = ψ (b i)) ∧
      LinearIndependent (FractionRing D) (fun i : e ↦
        cofiniteCoefficientBaseChangeCompletedDerivation (L := FractionRing D)
          (b := b) e (maximalIdeal D) ψ (ψ (b i))) ∧
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D) (cofiniteCoefficientDifferential (b := b) e ψ)) =
        h + e.card := by
  classical
  let : Algebra (ResidueField D) D := φ.toAlgebra
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp φ)
    rw [hφ]
    exact Function.surjective_id
  obtain ⟨e, μ, hμ, hi, hdimold⟩ :=
    hb.exists_independent_coefficient_perturbation hdim hres hm z hzm hprimary
  let : IsAdicComplete (RingHom.ker (residue D)) D := by
    rw [ker_residue]
    infer_instance
  let ν : e → RingHom.ker (residue D) := fun i ↦ ⟨μ i, by simpa only [ker_residue] using hμ i⟩
  obtain ⟨ψ, hψ, hvalues, hagree⟩ := hb.exists_section_of_finitePerturbation
    (residue D) residue_surjective φ hφ e ν
  have heq : ∀ d : D,
      cofiniteCoefficientBaseChangeCompletedDerivation (L := FractionRing D)
        (b := b) e (maximalIdeal D) φ d =
      baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D) d := by
    intro d
    simp only [cofiniteCoefficientBaseChangeCompletedDerivation_apply,
      baseChangeCompletedKaehlerDerivation_apply, cofiniteKaehlerRestriction_D]
  have hiold : LinearIndependent (FractionRing D) (fun i : e ↦
      cofiniteCoefficientBaseChangeCompletedDerivation (L := FractionRing D)
        (b := b) e (maximalIdeal D) φ (ψ (b i))) := by
    simpa only [heq, hvalues, ν, RingHom.algebraMap_toAlgebra] using hi
  have hagree' : ∀ i, i ∉ e → φ (b i) = ψ (b i) := fun i h ↦ (hagree i h).symm
  let q := hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv
    e (maximalIdeal D) (FractionRing D) φ ψ hagree'
  have hinew := hiold.map' q.toLinearMap q.ker
  refine ⟨e, ψ, hψ, hagree', ?_, ?_⟩
  · dsimp only [q] at hinew
    simpa only [Function.comp_def, LinearEquiv.coe_coe,
      IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_derivation] using hinew
  · exact q.finrank_eq.symm.trans hdimold
end ResidueSection

end Independent

section CompletedDimension


section Dimension
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}

/-- 独立な有限係数方向を消すと、全係数体上の完備微分の次元はhとなる。 -/
theorem IsPBasis.finrank_completedKaehler_of_independent_coefficient_directions
    (hb : IsPBasis K p b) (e : Finset ι) {h : ℕ}
    (hres : Function.Surjective ((residue D).comp (algebraMap K D)))
    (hi : LinearIndependent (FractionRing D) (fun i : e ↦
      baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D)
          (algebraMap K D (b i))))
    (hdim : Module.finrank (FractionRing D) (FractionRing D ⊗[D]
      AdicCompletion (maximalIdeal D)
        (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) = h + e.card) :
    Module.finrank (FractionRing D) (FractionRing D ⊗[D]
      AdicCompletion (maximalIdeal D) (KaehlerDifferential K D)) = h := by
  classical
  let E := pBasisCofiniteField (p := p) b e
  let C := AdicCompletion (maximalIdeal D) (KaehlerDifferential E D)
  let : Module.Finite D C := hb.moduleFinite_completedKaehler_cofiniteField e hres
    (maximalIdeal D) (maximalIdeal.isMaximal D).isPrime.radical
  let g : C →ₗ[D] AdicCompletion (maximalIdeal D) (KaehlerDifferential K D) :=
    (AdicCompletion.map (maximalIdeal D) (KaehlerDifferential.map E K D D)).restrictScalars D
  have hg : Function.Surjective g :=
    AdicCompletion.map_surjective (maximalIdeal D) (KaehlerDifferential.map_surjective E K D)
  let f := g.baseChange (FractionRing D)
  have hf : Function.Surjective f := LinearMap.baseChange_surjective (FractionRing D) hg
  have hker : LinearMap.ker f = Submodule.span (FractionRing D) (Set.range (fun i : e ↦
      baseChangeCompletedKaehlerDerivation (k := E) (FractionRing D) (maximalIdeal D)
        (algebraMap K D (b i)))) :=
    ker_baseChange_eq_span_of_ker_eq_span (FractionRing D) g _
      (hb.ker_completed_cofiniteToFullKaehlerRestriction e (maximalIdeal D)
        (maximalIdeal_le_jacobson ⊥))
  have hkdim : Module.finrank (FractionRing D) (LinearMap.ker f) = e.card := by
    rw [hker, finrank_span_eq_card hi, Fintype.card_coe]
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hkdim] at h
  rw [hdim] at h
  omega
end Dimension

section Existence
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP D p] [CharP (ResidueField D) p]
  {ι : Type*} {b : ι → ResidueField D}

/-- 係数切断を変更し、全係数体上の完備微分の生成点の次元を環の次元へ減らす。 -/
theorem IsPBasis.exists_coefficient_section_completed_finrank
    (hb : IsPBasis (ResidueField D) p b)
    (φ : ResidueField D →+* D) (hφ : (residue D).comp φ = RingHom.id (ResidueField D))
    {h : ℕ} (hdim : ringKrullDim D = h) (hm : maximalIdeal D ≠ ⊥)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ ψ : ResidueField D →+* D,
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      letI : Algebra (ResidueField D) D := ψ.toAlgebra
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D) (KaehlerDifferential (ResidueField D) D)) = h := by
  obtain ⟨e, ψ, hψ, _, hi, hdimψ⟩ :=
    hb.exists_independent_coefficient_section φ hφ hdim hm z hzm hprimary
  refine ⟨ψ, hψ, ?_⟩
  let : Algebra (ResidueField D) D := ψ.toAlgebra
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp ψ)
    rw [hψ]
    exact Function.surjective_id
  have hi' : LinearIndependent (FractionRing D) (fun i : e ↦
      baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D)
          (algebraMap (ResidueField D) D (b i))) := by
    simpa only [cofiniteCoefficientBaseChangeCompletedDerivation_apply,
      cofiniteKaehlerRestriction_D, baseChangeCompletedKaehlerDerivation_apply,
      RingHom.algebraMap_toAlgebra] using hi
  exact hb.finrank_completedKaehler_of_independent_coefficient_directions e hres hi' hdimψ
end Existence

end CompletedDimension

end SerrePositivity
