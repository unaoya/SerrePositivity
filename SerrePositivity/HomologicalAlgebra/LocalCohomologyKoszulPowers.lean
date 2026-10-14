module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulStageZero
public import Mathlib.Algebra.Homology.LocalCohomology

/-! # Coordinate powers as a cofinal ideal system for actual local cohomology -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- Coordinatewise n-th powers generate a subideal of the n-th power of the span. -/
lemma powerKoszulIdeal_le_span_pow (n : ℕ) :
    powerKoszulIdeal R z n ≤ Ideal.span (Set.range z) ^ n := by
  apply Ideal.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) n

/-- All coordinate-power ideals have radical containing the support ideal. -/
lemma span_le_powerKoszulIdeal_radical (n : ℕ) :
    Ideal.span (Set.range z) ≤ (powerKoszulIdeal R z n).radical := by
  apply Ideal.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact Ideal.mem_radical_iff.mpr ⟨n, Ideal.subset_span (Set.mem_range_self j)⟩

/-- Conversely, each coordinate-power ideal contains a power of the support ideal. -/
lemma exists_span_pow_le_powerKoszulIdeal [hR : IsNoetherian R R] (n : ℕ) :
    ∃ m : ℕ, Ideal.span (Set.range z) ^ m ≤ powerKoszulIdeal R z n :=
  Ideal.exists_pow_le_of_le_radical_of_fg (span_le_powerKoszulIdeal_radical z n)
    (isNoetherian_def.mp hR _)

/-- The actual descending coordinate-power ideals, indexed contravariantly by natural numbers. -/
def powerKoszulIdealDiagram : ℕᵒᵖ ⥤ Ideal R where
  obj n := powerKoszulIdeal R z (unop n)
  map f := ⟨⟨powerKoszulIdeal_antitone R z f.unop.down.down⟩⟩

/-- The coordinate-power system in the category of ideals with the same support condition. -/
def powerKoszulToSelfLERadical : ℕᵒᵖ ⥤ localCohomology.SelfLERadical (Ideal.span (Set.range z)) :=
  ObjectProperty.lift _ (powerKoszulIdealDiagram z)
    (fun n => span_le_powerKoszulIdeal_radical z (unop n))

instance powerKoszulToSelfLERadical_initial [hR : IsNoetherian R R] :
    Functor.Initial (powerKoszulToSelfLERadical z) where
  out J' := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.property
        (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨(powerKoszulIdeal_le_span_pow z k).trans hk⟩⟩⟩ :
          (powerKoszulToSelfLERadical z).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

/-- The Ext colimit over coordinate powers is naturally Mathlib's actual local cohomology. -/
def localCohomologyPowerKoszulIdealNatIso [IsNoetherian R R] (i : ℕ) :
    localCohomology.ofDiagram (powerKoszulIdealDiagram z) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  localCohomology.isoOfFinal (powerKoszulToSelfLERadical z)
      (localCohomology.selfLERadicalDiagram (Ideal.span (Set.range z))) i ≪≫
    localCohomology.isoSelfLERadical (Ideal.span (Set.range z)) i

/-- Adjacent quotient arrows are the standard quotient transitions used by the Koszul tower. -/
lemma powerKoszulIdealDiagram_quotient_transition (n : ℕ) (r : R) :
    ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
      (homOfLE (Nat.le_succ n)).op).hom (Ideal.Quotient.mk _ r) =
      powerKoszulQuotientTransition R z n (Ideal.Quotient.mk _ r) := rfl

end SerrePositivity
