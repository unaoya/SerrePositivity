-- 境界例と、実際の有限評価の単射性・有限性・分離性を同じ型で確認する。
import SerrePositivity.Inputs.CohenNormalization
import SerrePositivity.CommutativeAlgebra.PowerSeriesCharacteristic
import Mathlib.Data.ZMod.Basic
import Mathlib.Util.AssertNoSorry

open SerrePositivity IsLocalRing
open scoped TensorProduct

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : IsAdicComplete (maximalIdeal (ZMod 2)) (ZMod 2) := by
  rw [maximalIdeal_eq_bot]
  infer_instance

-- 有限剰余体・h=0。極大イデアルが零の分岐を実際に適用する。
theorem cohenGabber_finiteField_boundary :
    ∃ (F : MvPowerSeries (Fin 0) (ResidueField (ZMod 2)) →+* ZMod 2)
      (hF : Function.Injective F), F.Finite ∧
      @Algebra.IsSeparable (FractionRing (MvPowerSeries (Fin 0) (ResidueField (ZMod 2))))
        (FractionRing (ZMod 2)) inferInstance inferInstance (fractionRingMap F hF).toAlgebra := by
  obtain ⟨F, hF, hfin, _, hsep⟩ := exists_cohen_gabber_powerSeries_map (ZMod 2)
    (ringKrullDim_eq_zero_of_field (ZMod 2)) 2
  exact ⟨F, hF, hfin, hsep⟩

-- 有限完全係数体・h=1。非零極大イデアルの分岐の適用。
theorem cohenGabber_oneVariable_boundary :
    let D := MvPowerSeries (Fin 1) (ZMod 2)
    ∃ (F : MvPowerSeries (Fin 1) (ResidueField D) →+* D)
      (hF : Function.Injective F), F.Finite ∧
      @Algebra.IsSeparable (FractionRing (MvPowerSeries (Fin 1) (ResidueField D)))
        (FractionRing D) inferInstance inferInstance (fractionRingMap F hF).toAlgebra := by
  let D := MvPowerSeries (Fin 1) (ZMod 2)
  let : IsAdicComplete (maximalIdeal D) D := isAdicComplete_powerSeries_maximalIdeal (Fin 1) (ZMod 2)
  obtain ⟨F, hF, hfin, _, hsep⟩ := exists_cohen_gabber_powerSeries_map D
    (by rw [ringKrullDim_mvPowerSeries_fin, ringKrullDim_eq_zero_of_field, zero_add]) 2
  exact ⟨F, hF, hfin, hsep⟩

-- 空の係数方向。添字ιには有限性を要求せず、無限p-basisでもこの式が成立する。
theorem cohenGabber_emptyCoefficient_boundary
    {K S ι : Type*} [Field K] [CommRing S] [Algebra K S] [IsNoetherianRing S]
    {p : ℕ} [Fact p.Prime] [CharP K p] {b : ι → K} (hb : IsPBasis K p b)
    (I : Ideal S) (hI : I ≤ Ideal.jacobson (⊥ : Ideal S))
    [Module.Finite S (AdicCompletion I
      (KaehlerDifferential (pBasisCofiniteField (p := p) b ∅) S))] :
    LinearMap.ker ((AdicCompletion.map I
      (KaehlerDifferential.map (pBasisCofiniteField (p := p) b ∅) K S S)).restrictScalars S) = ⊥ := by
  let : IsEmpty (↑(∅ : Finset ι)) := ⟨fun i ↦ Finset.notMem_empty _ i.property⟩
  have h := hb.ker_completed_cofiniteToFullKaehlerRestriction (∅ : Finset ι) I hI
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact h

-- p乗の微分だけを正の次元の微分空間の基底と誤認しない。
theorem cohenGabber_powers_do_not_span_boundary
    {R S L V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Field L] [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    (p : ℕ) [CharP S p] (δ : Derivation R S V) (z : Fin 1 → S)
    (hdim : Module.finrank L V = 1) :
    Submodule.span L (Set.range (fun i ↦ δ (z i ^ p))) ≠ ⊤ := by
  intro hspan
  have hzero : (⊥ : Submodule L V) = ⊤ := by
    simpa only [derivation_pow_char_eq_zero p δ, Set.range_const, Submodule.span_zero_singleton]
      using hspan
  have h := congrArg (fun P : Submodule L V ↦ Module.finrank L P) hzero
  simp only [finrank_bot, finrank_top, hdim] at h
  omega

#print axioms cohenGabber_finiteField_boundary
assert_no_sorry cohenGabber_finiteField_boundary
#print axioms cohenGabber_oneVariable_boundary
assert_no_sorry cohenGabber_oneVariable_boundary
#print axioms cohenGabber_emptyCoefficient_boundary
assert_no_sorry cohenGabber_emptyCoefficient_boundary
#print axioms cohenGabber_powers_do_not_span_boundary
assert_no_sorry cohenGabber_powers_do_not_span_boundary
#print axioms SerrePositivity.Inputs.cohen_gabber_normalization
assert_no_sorry SerrePositivity.Inputs.cohen_gabber_normalization
