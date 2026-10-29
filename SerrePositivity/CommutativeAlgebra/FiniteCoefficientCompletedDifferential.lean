module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionKernelClosure
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficientRestriction
public import Mathlib.RingTheory.Flat.Equalizer
public import SerrePositivity.RingTheory.Derivation

/-! # 有限係数方向に沿う完備微分の核

完備中項の有限性から像の閉包を除く。終域の有限型性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct

section Completion
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- 全射はイデアル進完備化の全射を誘導する。 -/
theorem adicCompletion_map_surjective_of_surjective (I : Ideal R) (g : M →ₗ[R] N)
    (hg : Function.Surjective g) : Function.Surjective (AdicCompletion.map I g) :=
  AdicCompletion.map_surjective_of_mkQ_comp_surjective
    ((I • (⊤ : Submodule R N)).mkQ_surjective.comp hg)

/-- 完備中項が有限なら、有限族で生成された核も同じ族の完備化の像で生成される。 -/
theorem ker_adicCompletion_map_eq_span_of_ker_eq_span [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R (AdicCompletion I M)]
    (g : M →ₗ[R] N) (hg : Function.Surjective g)
    {ι : Type*} (c : ι → M) (hker : LinearMap.ker g = Submodule.span R (Set.range c)) :
    LinearMap.ker ((AdicCompletion.map I g).restrictScalars R) =
      Submodule.span R (Set.range (fun i ↦ AdicCompletion.of I M (c i))) := by
  let : TopologicalSpace (AdicCompletion I M) := I.adicModuleTopology (AdicCompletion I M)
  let P := Submodule.span R (Set.range (fun i ↦ AdicCompletion.of I M (c i)))
  let : IsHausdorff I (AdicCompletion I M ⧸ P) := IsHausdorff.of_le_jacobson I _ hI
  have hc := isClosed_submodule_adic_of_hausdorff_quotient I P
  have he := closure_ker_image_eq_ker_adicCompletion_map I I.fg_of_isNoetherianRing g hg
  rw [hker, Submodule.map_span, ← Set.range_comp] at he
  change closure (P : Set (AdicCompletion I M)) = _ at he
  rw [hc.closure_eq] at he
  exact SetLike.coe_injective he.symm

/-- 平坦な係数拡大で核の生成族を同じテンソルの像へ移す。 -/
theorem ker_baseChange_eq_span_of_ker_eq_span
    (L : Type*) [CommRing L] [Algebra R L] [Module.Flat R L]
    (g : M →ₗ[R] N) {ι : Type*} (c : ι → M)
    (hker : LinearMap.ker g = Submodule.span R (Set.range c)) :
    LinearMap.ker (g.baseChange L) = Submodule.span L
      (Set.range (fun i ↦ (1 : L) ⊗ₜ[R] c i)) := by
  change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L g) = _
  rw [Module.Flat.ker_lTensor_eq]
  change (LinearMap.ker g).baseChange L = _
  rw [hker, Submodule.baseChange_span, ← Set.range_comp]
  rfl
end Completion

section Coefficients
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
end Coefficients

end SerrePositivity
