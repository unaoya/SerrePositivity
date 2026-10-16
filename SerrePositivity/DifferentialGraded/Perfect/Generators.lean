module
public import SerrePositivity.DifferentialGraded.Perfect.PerfectCompact
public import SerrePositivity.DifferentialGraded.Derived.AcyclicZero
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Logic.Small.Set

/-! # 代表加群の整数shiftによる主導来圏のcompact生成性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleEvaluationShiftHomologyIso (x : D) (N : ModuleCategory A D) (n : ℤ) :
    ((moduleEvaluation A D x).obj (N⟦n⟧)).homology 0 ≅
      ((moduleEvaluation A D x).obj N).homology n :=
  HomologicalComplex.homologyMapIso (((moduleEvaluation A D x).commShiftIso n).app N) 0 ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat A) n 0 n (by omega)).app
      ((moduleEvaluation A D x).obj N)

lemma moduleRepresentables_detect_zero (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ (x : D) (n : ℤ), Subsingleton
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X⟦n⟧) := by
  constructor
  · intro hX x n
    exact ⟨fun f g => ((shiftFunctor (DerivedModuleCategory A D) n).map_isZero hX).eq_of_tgt f g⟩
  · intro hX
    obtain ⟨⟨N⟩⟩ := X
    apply moduleToDerived_isZero_of_acyclic A D
    intro x n
    have : Subsingleton
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
          (moduleToDerived A D).obj (N⟦n⟧)) :=
      ⟨fun f g =>
        (Iso.homCongr (Iso.refl _) (((moduleToDerived A D).commShiftIso n).app N)).injective
          (@Subsingleton.elim _ (hX x n) _ _)⟩
    have : Subsingleton (((moduleEvaluation A D x).obj (N⟦n⟧)).homology 0) :=
      (moduleRepresentableDerivedHomologyEquiv A D x (N⟦n⟧)).symm.injective.subsingleton
    have : Subsingleton (((moduleEvaluation A D x).obj N).homology n) :=
      (moduleEvaluationShiftHomologyIso A D x N n).toLinearEquiv.symm.injective.subsingleton
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)

lemma moduleRepresentableShifts_detect_zero (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ (x : D) (n : ℤ), Subsingleton
      (((moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x)))⟦n⟧ ⟶ X) := by
  constructor
  · intro hX x n
    exact ⟨fun f g => hX.eq_of_tgt f g⟩
  · intro hX
    apply (moduleRepresentables_detect_zero A D X).mpr
    intro x n
    let e := (shiftEquiv' (DerivedModuleCategory A D) (-n) n
      (neg_add_cancel n)).toAdjunction.homEquiv
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x))) X
    exact ⟨fun f g => e.symm.injective (@Subsingleton.elim _ (hX x (-n)) _ _)⟩

def moduleCompactGenerators (p : D × ℤ) : DerivedModuleCategory A D :=
  ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A p.1)))⟦p.2⟧

lemma moduleCompactGenerators_small : Small.{u} (Set.range (moduleCompactGenerators A D)) := by
  infer_instance

lemma moduleCompactGenerators_compact (p : D × ℤ) :
    moduleCompact A D (moduleCompactGenerators A D p) :=
  moduleCompact_shift A D (moduleRepresentable_compact A D p.1) p.2

lemma moduleCompactGenerators_detect_zero (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ p : D × ℤ, Subsingleton (moduleCompactGenerators A D p ⟶ X) := by
  rw [moduleRepresentableShifts_detect_zero]
  constructor
  · intro h p
    exact h p.1 p.2
  · intro h x n
    exact h (x, n)

end SerrePositivity.DifferentialGraded
