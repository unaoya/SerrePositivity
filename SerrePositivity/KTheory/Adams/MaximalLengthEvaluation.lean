module

public import SerrePositivity.KTheory.Adams.MaximalSupportModules
public import SerrePositivity.KTheory.G0Functoriality
public import SerrePositivity.PerfectComplex.IntegerEuler
public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Local length evaluations on maximal support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory IsLocalRing TensorProduct
namespace Adams
variable {R : Type u} [CommRing R]
variable (W : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hw : ∀ p ∈ W, p.asIdeal.IsMaximal)

include hw in
/-- Localization of maximal support is supported at the maximal ideal of the local ring. -/
lemma maximalSupport_pullback_le (p : PrimeSpectrum R) :
    supportPullback (algebraMap R (Localization.AtPrime p.asIdeal)) W ≤
      supportZeroLocus (maximalIdeal (Localization.AtPrime p.asIdeal)) := by
  let T := Localization.AtPrime p.asIdeal
  intro q hq
  let r := PrimeSpectrum.comap (algebraMap R T) q
  have hle : r.asIdeal ≤ p.asIdeal := by
    calc
      _ ≤ (maximalIdeal T).under R := Ideal.comap_mono (le_maximalIdeal q.isPrime.ne_top)
      _ = _ := IsLocalization.AtPrime.under_maximalIdeal T p.asIdeal
  have he : r.asIdeal = p.asIdeal := (hw r hq).eq_of_le p.isPrime.ne_top hle
  have hc : (maximalIdeal T).under R = q.asIdeal.under R :=
    (IsLocalization.AtPrime.under_maximalIdeal T p.asIdeal).trans he.symm
  have heq : maximalIdeal T = q.asIdeal :=
    (IsLocalization.orderEmbedding p.asIdeal.primeCompl T).injective hc
  exact heq.le

variable [IsNoetherianRing R]

/-- The integer length at one prime, defined by flat localization and the existing length map. -/
def localLengthMap (p : PrimeSpectrum R) : G0WithSupport W →+ ℤ :=
  (maximalSupportLengthMap (Localization.AtPrime p.asIdeal)).comp
    (G0WithSupport.map (algebraMap R (Localization.AtPrime p.asIdeal))
      (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat _ p.asIdeal.primeCompl)
      W (supportZeroLocus (maximalIdeal (Localization.AtPrime p.asIdeal)))
      (maximalSupport_pullback_le W hw p))

lemma localLengthMap_mk (p : PrimeSpectrum R) (M : SupportedFGModuleOn W) :
    localLengthMap W hw p (G0WithSupport.mk M) =
      ((Module.length (Localization.AtPrime p.asIdeal)
        ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime p.asIdeal))).obj M.obj)).toNat :
        ℤ) := by
  simp only [localLengthMap, AddMonoidHom.comp_apply, G0WithSupport.map_mk,
    maximalSupportLengthMap_mk]

lemma localLengthMap_residue_self (p : PrimeSpectrum R) (hm : p.asIdeal.IsMaximal)
    (hp : p ∈ W) :
    localLengthMap W hw p (G0WithSupport.mk (supportedResidueModule W p hm hp)) = 1 := by
  rw [localLengthMap_mk]
  let T := Localization.AtPrime p.asIdeal
  have : IsSimpleModule T (T ⧸ maximalIdeal T) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal T).out
  rw [(extendScalarsObjEquivTensor R T (supportedResidueModule W p hm hp).obj).length_eq]
  change ((Module.length T (T ⊗[R] (R ⧸ p.asIdeal))).toNat : ℤ) = 1
  rw [← (p.asIdeal.quotMapEquivTensorQuot T).length_eq,
    IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal T, Module.length_eq_one]
  rfl

lemma localLengthMap_residue_ne (p q : PrimeSpectrum R) (hm : q.asIdeal.IsMaximal)
    (hq : q ∈ W) (hne : p ≠ q) :
    localLengthMap W hw p (G0WithSupport.mk (supportedResidueModule W q hm hq)) = 0 := by
  rw [localLengthMap_mk]
  let T := Localization.AtPrime p.asIdeal
  have hnot : ¬ q.asIdeal ≤ p.asIdeal := by
    intro hle
    exact hne (PrimeSpectrum.ext (hm.eq_of_le p.isPrime.ne_top hle)).symm
  obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hnot
  have ht : q.asIdeal.map (algebraMap R T) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hs)
      (IsLocalization.map_units (M := p.asIdeal.primeCompl) T ⟨s, hsp⟩)
  rw [(extendScalarsObjEquivTensor R T (supportedResidueModule W q hm hq).obj).length_eq]
  change ((Module.length T (T ⊗[R] (R ⧸ q.asIdeal))).toNat : ℤ) = 0
  rw [← (q.asIdeal.quotMapEquivTensorQuot T).length_eq, ht]
  simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]

open Classical in
lemma localLengthMap_residue (p q : PrimeSpectrum R) (hm : q.asIdeal.IsMaximal)
    (hq : q ∈ W) :
    localLengthMap W hw p (G0WithSupport.mk (supportedResidueModule W q hm hq)) =
      if p = q then 1 else 0 := by
  classical
  by_cases he : p = q
  · subst q
    rw [localLengthMap_residue_self, ite_eq_left rfl]
  · rw [localLengthMap_residue_ne W hw p q hm hq he, ite_eq_right he]

/-- Simultaneous local length evaluation at all points of the maximal support. -/
def maximalLengthEvaluation : G0WithSupport W →+ ({p : PrimeSpectrum R // p ∈ W} → ℤ) where
  toFun x p := localLengthMap W hw p.val x
  map_zero' := by funext p; exact (localLengthMap W hw p.val).map_zero
  map_add' x y := by funext p; exact (localLengthMap W hw p.val).map_add x y

@[simp]
lemma maximalLengthEvaluation_apply (x : G0WithSupport W) (p : {p : PrimeSpectrum R // p ∈ W}) :
    maximalLengthEvaluation W hw x p = localLengthMap W hw p.val x := rfl

end Adams
end SerrePositivity
