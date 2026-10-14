module

public import SerrePositivity.CommutativeAlgebra.CompletedDifferentialGeneration
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficientDifferential
public import Mathlib.RingTheory.Localization.FractionRing

/-! # 中間係数体上の完備微分の生成点での生成性

通常正規化や分離的正規化を入力に要求しない。
係数体の共通剰余体から完備微分の有限性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
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

end SerrePositivity
