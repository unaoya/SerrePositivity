module
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Finite termwise induction for Koszul acyclicity of bounded complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [CommRing C]

/-- The existing termwise cutoff sequence is actually short exact. -/
lemma stupidTruncation_module_shortExact (K : CochainComplex (ModuleCat.{u} C) ℤ) (a : ℤ) :
    (StupidTruncation.shortComplex K a).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  exact (StupidTruncation.splitting K a q).shortExact

/-- Koszul-acyclic endpoints force an acyclic middle through the actual homology sequence. -/
lemma koszulShortExact_middle_homology_isZero {r : ℕ} (y : Fin r → C)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ)) (hS : S.ShortExact)
    (h₁ : ∀ p : ℤ, IsZero ((koszulComplexOn y S.X₁).homology p))
    (h₃ : ∀ p : ℤ, IsZero ((koszulComplexOn y S.X₃).homology p)) (p : ℤ) :
    IsZero ((koszulComplexOn y S.X₂).homology p) :=
  ((koszulFunctor_shortExact y S hS).homology_exact₂ p).isZero_X₂
    ((h₁ p).eq_zero_of_src _) ((h₃ p).eq_zero_of_tgt _)

/-- Truncating a complex at its lower bound leaves the actual boundary term alone. -/
def stupidTruncation_belowSingleIso (K : CochainComplex (ModuleCat.{u} C) ℤ) (a : ℤ)
    (hK : ∀ q, q < a → IsZero (K.X q)) :
    StupidTruncation.below K a ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} C) a).obj (K.X a) := by
  have hz (q : ℤ) (hq : q ≠ a) : IsZero ((StupidTruncation.below K a).X q) := by
    by_cases hqa : q ≤ a
    · exact (hK q (by omega)).of_iso (StupidTruncation.belowXIso K a q hqa)
    · exact StupidTruncation.below_isZero_X K a q (by omega)
  refine Hom.isoOfComponents (fun q => if hq : q = a then ?_ else
    (hz q hq).iso (isZero_single_obj_X (.up ℤ) a (K.X a) q hq)) ?_
  · subst q
    exact StupidTruncation.belowXIso K a a le_rfl ≪≫
      (singleObjXSelf (.up ℤ) a (K.X a)).symm
  · intro i j hij
    by_cases hi : i = a
    · have hj : j ≠ a := by change i + 1 = j at hij; omega
      exact (isZero_single_obj_X (.up ℤ) a (K.X a) j hj).eq_of_tgt _ _
    · exact (hz i hi).eq_of_src _ _

/-- Koszul-acyclic module coefficients remain acyclic when placed in any integer degree. -/
lemma koszulSingle_homology_isZero {r : ℕ} (y : Fin r → C) (M : ModuleCat.{u} C)
    (hM : ∀ p : ℤ, IsZero (((koszulModuleFunctor y).obj M).homology p)) (a p : ℤ) :
    IsZero ((koszulComplexOn y
      ((CochainComplex.singleFunctor (ModuleCat.{u} C) a).obj M)).homology p) := by
  let E := ((CochainComplex.singleFunctors (ModuleCat.{u} C)).shiftIso
    (-a) a 0 (by omega)).app M
  let E' := (koszulFunctor y).mapIso E.symm ≪≫
    (koszulComplexOnShiftIso y
      ((CochainComplex.singleFunctor (ModuleCat.{u} C) 0).obj M) (-a)).symm
  exact (hM (p - a)).of_iso
    ((homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso E' ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C)
        (-a) p (p - a) (by omega)).app ((koszulModuleFunctor y).obj M))

/-- A bounded complex of parameter-Koszul-acyclic terms is itself Koszul-acyclic.
The induction uses the actual termwise cutoff short exact sequences. -/
lemma boundedTermKoszul_homology_isZero {r : ℕ} (y : Fin r → C) :
    ∀ (N : ℕ) (K : CochainComplex (ModuleCat.{u} C) ℤ) (a : ℤ),
    (∀ q, q < a → IsZero (K.X q)) →
    (∀ q, a + (N : ℤ) ≤ q → IsZero (K.X q)) →
    (∀ q p : ℤ, IsZero (((koszulModuleFunctor y).obj (K.X q)).homology p)) →
    ∀ p : ℤ, IsZero ((koszulComplexOn y K).homology p)
  | 0, K, a, hlo, hhi, _, p => by
    have hK : IsZero K := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext q
      by_cases hq : q < a
      · exact (hlo q hq).eq_of_src _ _
      · exact (hhi q (by simpa using le_of_not_gt hq)).eq_of_src _ _
    exact ((koszulFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).map_isZero hK
  | N + 1, K, a, hlo, hhi, hterms, p => by
    have htail := boundedTermKoszul_homology_isZero y N
      (StupidTruncation.above K (a + 1)) (a + 1)
      (StupidTruncation.above_isZero_X K (a + 1))
      (fun q hq => (hhi q (by omega)).of_iso
        (StupidTruncation.aboveXIso K (a + 1) q (by omega))) (by
          intro q p
          by_cases hq : a + 1 ≤ q
          · exact (hterms q p).of_iso
              (((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso
                (StupidTruncation.aboveXIso K (a + 1) q hq))
          · exact ((koszulModuleFunctor y) ⋙
                homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).map_isZero
              (StupidTruncation.above_isZero_X K (a + 1) q (by omega)))
    have hbelow (p : ℤ) : IsZero
        ((koszulComplexOn y (StupidTruncation.below K a)).homology p) :=
      (koszulSingle_homology_isZero y (K.X a) (hterms a) a p).of_iso
        ((homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso
          ((koszulFunctor y).mapIso (stupidTruncation_belowSingleIso K a hlo)))
    apply koszulShortExact_middle_homology_isZero y
      (StupidTruncation.shortComplex K (a + 1))
      (stupidTruncation_module_shortExact K (a + 1)) htail _ p
    intro q
    simpa only [StupidTruncation.shortComplex, add_sub_cancel_right] using hbelow q

end SerrePositivity
