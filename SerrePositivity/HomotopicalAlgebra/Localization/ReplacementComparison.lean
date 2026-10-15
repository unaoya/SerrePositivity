module

public import SerrePositivity.HomotopicalAlgebra.Localization.ReplacementData
public import SerrePositivity.HomotopicalAlgebra.Localization.ChoiceIndependence

/-! # Natural comparison of local replacements and nested localization

The common comparison is the actual composite of the two functors. For
equal localization classes both legs are original weak equivalences.
For S ≤ T, either composite absorbs the S-replacement up to such a natural
weak equivalence. These statements require no chosen common lifts.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))


namespace LocalReplacementData
variable {cof fib} {S T : MorphismProperty C}
  (d : LocalReplacementData cof fib S) (e : LocalReplacementData cof fib T)

abbrev common : C ⥤ C := d.L ⋙ e.L
abbrev compareLeft : d.L ⟶ common d e := Functor.whiskerLeft d.L e.η
abbrev compareRight : e.L ⟶ common d e := Functor.whiskerRight d.η e.L

lemma compare_under : d.η ≫ compareLeft d e = e.η ≫ compareRight d e := by
  ext X
  exact e.η.naturality (d.η.app X)

variable (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma compareRight_weakEquivalence_of_le (h : S ≤ T) (X : C) :
    weakEquivalences C ((compareRight d e).app X) :=
  (e.map_mem_iff hcof hfib _).mpr
    (MappingTests.localEquivalences_monotone _ _ h _ (d.unit_localEquivalence X))

include hcof hfib in
lemma compareLeft_weakEquivalence_of_ge (h : T ≤ S) (X : C) :
    weakEquivalences C ((compareLeft d e).app X) :=
  e.unit_weakEquivalence_of_local hcof hfib _
    (MappingTests.localObjects_antitone _ _ h (d.localFibrant X).2)

include hcof hfib in
lemma comparison_weakEquivalences (e' : LocalReplacementData cof fib S) (X : C) :
    weakEquivalences C ((compareLeft d e').app X) ∧
      weakEquivalences C ((compareRight d e').app X) :=
  ⟨compareLeft_weakEquivalence_of_ge d e' hcof hfib le_rfl X,
    compareRight_weakEquivalence_of_le d e' hcof hfib le_rfl X⟩



/-- Transport actual replacement data across the proved mapping-space choice equality. -/
def changeChoices
    (cof' : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib' : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    LocalReplacementData cof' fib' S where
  L := d.L
  η := d.η
  unit_cofibration := d.unit_cofibration
  unit_localEquivalence X :=
    (localEquivalences_choices_eq cof cof' fib fib' hcof S).le _ (d.unit_localEquivalence X)
  localFibrant X :=
    (congrArg (fun P : C → Prop => P (d.L.obj X))
      (localFibrantObjects_choices_eq cof cof' fib fib' hcof S)).mp (d.localFibrant X)

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

/-- The T-replacement absorbs a preceding S-replacement, naturally in Ho(C). -/
def compareRightLocalizationIso_of_le (h : S ≤ T) :
    e.L ⋙ Q ≅ common d e ⋙ Q := by
  let a := Functor.whiskerRight (compareRight d e) Q
  have (X : C) : IsIso (a.app X) := Localization.inverts Q (weakEquivalences C) _
    (compareRight_weakEquivalence_of_le d e hcof hfib h X)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

/-- The S-replacement absorbs a following T-replacement when T ≤ S. -/
def compareLeftLocalizationIso_of_ge (h : T ≤ S) :
    d.L ⋙ Q ≅ common d e ⋙ Q := by
  let a := Functor.whiskerRight (compareLeft d e) Q
  have (X : C) : IsIso (a.app X) := Localization.inverts Q (weakEquivalences C) _
    (compareLeft_weakEquivalence_of_ge d e hcof hfib h X)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

/-- A natural isomorphism comparing any two actual local replacements in Ho(C). -/
def localizationIso (e' : LocalReplacementData cof fib S) : d.L ⋙ Q ≅ e'.L ⋙ Q :=
  (compareLeftLocalizationIso_of_ge d e' hcof hfib Q le_rfl).trans
    (compareRightLocalizationIso_of_le d e' hcof hfib Q le_rfl).symm

end LocalReplacementData
end SerrePositivity.Bousfield
