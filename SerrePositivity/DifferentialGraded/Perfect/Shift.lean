module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift

/-! # finite cellとPerfの整数shift閉性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleFiniteCellOverStableUnderShift (S : Set D) :
    (moduleFiniteCellOver A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ hM => moduleFiniteCellOver_shift A D hM s⟩

instance derivedFiniteCellOverStableUnderShift (S : Set D) :
    (derivedFiniteCellOver A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨by
    rintro X ⟨M, hM, ⟨e⟩⟩
    exact ⟨M⟦s⟧, moduleFiniteCellOver_shift A D hM s,
      ⟨((moduleToDerived A D).commShiftIso s).app M ≪≫
        (shiftFunctor (DerivedModuleCategory A D) s).mapIso e⟩⟩⟩

instance modulePerfectOverStableUnderShift (S : Set D) :
    (modulePerfectOver A D S).IsStableUnderShift ℤ := by
  dsimp [modulePerfectOver]
  infer_instance

lemma modulePerfectOver_shift {S : Set D} {X : DerivedModuleCategory A D}
    (hX : modulePerfectOver A D S X) (s : ℤ) : modulePerfectOver A D S (X⟦s⟧) :=
  (modulePerfectOver A D S).le_shift s X hX

lemma modulePerfect_shift {X : DerivedModuleCategory A D}
    (hX : modulePerfect A D X) (s : ℤ) : modulePerfect A D (X⟦s⟧) :=
  modulePerfectOver_shift A D hX s

/-- 既存の充満部分圏shiftを使う包含関手はzero/add coherenceを保つ。 -/
instance perfectModuleInclusionCommShift (S : Set D) :
    (perfectModuleInclusion A D S).CommShift ℤ := by
  dsimp [perfectModuleInclusion]
  infer_instance

instance modulePerfectStableUnderShift : (modulePerfect A D).IsStableUnderShift ℤ :=
  modulePerfectOverStableUnderShift A D Set.univ

end SerrePositivity.DifferentialGraded
