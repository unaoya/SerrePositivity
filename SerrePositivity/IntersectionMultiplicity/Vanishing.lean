module

public import SerrePositivity.CommutativeAlgebra.ModuleSupportHeight
public import SerrePositivity.KTheory.Adams.CupVanishing
public import SerrePositivity.PerfectComplex.TensorTorComparison
public import SerrePositivity.PerfectComplex.CoefficientEuler
public import SerrePositivity.KTheory.Adams.CyclicTwoFamily
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import SerrePositivity.CommutativeAlgebra.CubicCyclotomic.LocalExtension
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.KTheory.Adams.CyclicThreeFamily
public import SerrePositivity.KTheory.Adams.CubicCoefficientField

/-! # 台つき Adams 作用素による交点重複度の消滅

## 概要

台つきの Adams 作用素の族があれば交点重複度は消え（論文 (5.1)、Roberts–Gillet–Soulé）、剰余標数 2 以外では二乗の作用素、剰余標数 2 では 1 の原始三乗根を持つ局所拡大上の巡回三乗の作用素を使って、全ての剰余標数で `intersectionVanishing_of_adams` を示す。三次円分の局所拡大への消滅の仮定の移送も与える。

## 方針

重みの消滅から Euler 標数の消滅を導く。剰余標数 2 の場合は CommutativeAlgebra/CubicCyclotomic の局所拡大へ移る（長さ・次元・正則性と交点重複度は保存される）。

## 規約

一本の鎖として読む。

## 使われ方

IntersectionMultiplicity/Additivity、Paper の §5。
-/

@[expose] public noncomputable section

universe u v

section AdamsVanishingPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct IsLocalRing
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {E : Type v} [Field E] [CharZero E] {p : ℕ}

/-- A proved family of supported Adams operators implies the integer-valued vanishing theorem. -/
theorem intersectionVanishing_of_adamsFamily (F : Adams.LocalizationAdamsFamily R E p)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    chi R M N = 0 := by
  obtain ⟨cM, cN, hM, hN, hc⟩ := exists_supportHeight_sum_gt (R := R) M N hdim
  let FM := chosenPerfectModuleResolution (ModuleCat.of R M)
  let FN := chosenPerfectModuleResolution (ModuleCat.of R N)
  let x := FM.k0Class (finiteModuleClosedSupport R M) (support_subset_finiteModuleClosedSupport R M)
  let y := FN.k0Class (finiteModuleClosedSupport R N) (support_subset_finiteModuleClosedSupport R N)
  let h := finiteModuleClosedSupport_inf_le_maximal R M N hfin
  have hz := F.cup_enlarge_eq_zero (dimToNat (ringKrullDim R))
    (natCast_dimToNat_ringKrullDim R).symm
    (finiteModuleClosedSupport R M) (finiteModuleClosedSupport R N) cM cN hM hN hc h
    ((1 : E) ⊗ₜ[ℤ] x) ((1 : E) ⊗ₜ[ℤ] y)
  apply (integerEuler_cup_resolutions_of_finiteTensor FM FN hfin).symm.trans
  apply K0WithSupport.integerEuler_eq_zero_of_one_tmul_eq_zero E R
  simpa only [K0WithSupport.coefficientCup_tmul, one_mul,
    K0WithSupport.coefficientEnlarge_tmul] using hz

end SerrePositivity

end AdamsVanishingPart

section AdamsVanishingTwoPart

namespace SerrePositivity
open IsLocalRing TensorProduct
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A residue-field nonzero 2 supplies the inverse needed by the cyclic Adams square. -/
lemma isUnit_two_of_residue_ne_zero (h : (2 : ResidueField R) ≠ 0) : IsUnit (2 : R) := by
  apply (residue_ne_zero_iff_isUnit (2 : R)).mp
  simpa only [map_ofNat] using h

/-- The original hypotheses imply vanishing when residue 2 is nonzero. -/
theorem intersectionVanishing_of_residue_two_ne_zero
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R)
    (htwo : (2 : ResidueField R) ≠ 0) : chi R M N = 0 := by
  let : Invertible (2 : R) := (isUnit_two_of_residue_ne_zero htwo).invertible
  exact intersectionVanishing_of_adamsFamily (Adams.cyclicTwoFamily ℚ) M N hfin hdim

end SerrePositivity

end AdamsVanishingTwoPart

section CubicCyclotomicBaseChangePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open Polynomial IsLocalRing TensorProduct
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)
    [Fact (Irreducible g)]

-- Use the R-action specified by the structural R-algebra, as in the preservation API.
local instance : Module R (CubicCyclotomicLocalRing g h hf) := Algebra.toModule

/-- All numerical hypotheses and the integer intersection value transfer to the same local model. -/
lemma cubicCyclotomicLocalRing_vanishing_data (hc : IsCoprime g h)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    let B := CubicCyclotomicLocalRing g h hf
    Module.Finite B (B ⊗[R] M) ∧ Module.Finite B (B ⊗[R] N) ∧
      Module.length B ((B ⊗[R] M) ⊗[B] (B ⊗[R] N)) ≠ ⊤ ∧
      Module.supportDim B (B ⊗[R] M) + Module.supportDim B (B ⊗[R] N) < ringKrullDim B ∧
      chi B (B ⊗[R] M) (B ⊗[R] N) = chi R M N := by
  let B := CubicCyclotomicLocalRing g h hf
  have hm := residueFactorLocalRing_map_maximalIdeal _ g h
    (cubicCyclotomicPolynomial_map_residue_eq g h hf) hc
  refine ⟨inferInstance, inferInstance, ?_, ?_,
    chi_baseChange_of_map_maximalIdeal R B hm M N⟩
  · rw [tensorLength_baseChange_of_map_maximalIdeal R B hm M N]
    exact hfin
  · rw [supportDim_baseChange_of_map_maximalIdeal R B hm M,
      supportDim_baseChange_of_map_maximalIdeal R B hm N,
      residueFactorLocalRing_dimension _ g h
        (cubicCyclotomicPolynomial_map_residue_eq g h hf) hc]
    exact hdim

end SerrePositivity

end CubicCyclotomicBaseChangePart

section AdamsVanishingThreePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open Polynomial IsLocalRing TensorProduct
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Apply the cubic family on a chosen coprime-factor local model and preserve chi. -/
theorem intersectionVanishing_of_cubicCyclotomic_factor
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)
    [Fact (Irreducible g)] (hc : IsCoprime g h)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R)
    (htwo : (2 : ResidueField R) = 0) : chi R M N = 0 := by
  let B := CubicCyclotomicLocalRing g h hf
  let : Module R B := Algebra.toModule
  let : IsRegularLocalRing B :=
    residueFactorLocalRing_regular _ g h (cubicCyclotomicPolynomial_map_residue_eq g h hf) hc
  let : Invertible (3 : B) := (cubicCyclotomicLocalRing_three_isUnit g h hf htwo).invertible
  obtain ⟨hM, hN, hfinB, hdimB, hchi⟩ :=
    cubicCyclotomicLocalRing_vanishing_data g h hf hc M N hfin hdim
  let : Module.Finite B (B ⊗[R] M) := hM
  let : Module.Finite B (B ⊗[R] N) := hN
  have hz := intersectionVanishing_of_adamsFamily
    (Adams.cyclicThreeFamily Adams.CubicCoefficientField (cubicCyclotomicLocalRoot g h hf)
      (cubicCyclotomicLocalRoot_relation g h hf)
      Adams.cubicCoefficientRoot Adams.cubicCoefficientRoot_relation)
    (B ⊗[R] M) (B ⊗[R] N) hfinB hdimB
  exact hchi.symm.trans hz

/-- The original hypotheses imply vanishing when residue 2 is zero. -/
theorem intersectionVanishing_of_residue_two_eq_zero
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R)
    (htwo : (2 : ResidueField R) = 0) : chi R M N = 0 := by
  obtain ⟨g, h, _, hi, hf, hc, _⟩ := exists_cubicCyclotomic_coprime_factor htwo
  let : Fact (Irreducible g) := ⟨hi⟩
  exact intersectionVanishing_of_cubicCyclotomic_factor g h hf hc M N hfin hdim htwo

end SerrePositivity

end AdamsVanishingThreePart

section AdamsVanishingAllPart

namespace SerrePositivity
open IsLocalRing TensorProduct
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- The Roberts–Gillet–Soulé vanishing theorem proved using the cyclic Adams square and cube. -/
theorem intersectionVanishing_of_adams
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    chi R M N = 0 := by
  by_cases htwo : (2 : ResidueField R) = 0
  · exact intersectionVanishing_of_residue_two_eq_zero M N hfin hdim htwo
  · exact intersectionVanishing_of_residue_two_ne_zero M N hfin hdim htwo

end SerrePositivity

end AdamsVanishingAllPart
