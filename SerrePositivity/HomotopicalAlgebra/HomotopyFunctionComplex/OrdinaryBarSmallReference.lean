module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom

/-! # Actual weak maps from the large bar to small Kan reference values

The choices retain the exact localized comparison. No naturality of the
chosen actual maps, or strict simplicial action on the selected values, is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev value (X : Cᵒᵖ × C) : SSet.{v} :=
  (ReplacementMapping.uncurried hcof hfib).obj (ReplacementMapping.ofBase X)

lemma value_kan (X : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (value hcof hfib X)) :=
  (SSet.modelCategoryQuillen.fibration_iff _).mp
    (ReplacementMapping.kanComplex hcof hfib
      (ReplacementMapping.ofBase X).1 (ReplacementMapping.ofBase X).2)

def comparisonIso (X : Cᵒᵖ × C) :
    AnodyneHomotopy.anodyneQ.obj (UniverseLift.obj.{max u v} (value hcof hfib X)) ≅
      AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) :=
  OrdinaryBarReplacementComparison.presentationIso hcof hfib AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)
    (ReplacementMapping.ofBase X)

/-- This is an actual map, chosen to represent the original comparison inverse. -/
def toReference (X : Cᵒᵖ × C) : OrdinaryResolutionBar.functor.obj X ⟶
    UniverseLift.obj.{max u v} (value hcof hfib X) :=
  KanLocalizedRepresentatives.representative AnodyneHomotopy.anodyneQ
    (UniverseLift.horn_terminal_map (value_kan hcof hfib X))
    (comparisonIso hcof hfib X).inv

lemma toReference_map (X : Cᵒᵖ × C) :
    AnodyneHomotopy.anodyneQ.map (toReference hcof hfib X) =
      (comparisonIso hcof hfib X).inv :=
  KanLocalizedRepresentatives.representative_map _ _ _

lemma toReference_isIso (X : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toReference hcof hfib X)) := by
  rw [toReference_map]
  infer_instance

/-- Any other representative of that same inverse is connected by an actual interval. -/
lemma toReference_homotopy (X : Cᵒᵖ × C)
    (f : OrdinaryResolutionBar.functor.obj X ⟶
      UniverseLift.obj.{max u v} (value hcof hfib X))
    (hf : AnodyneHomotopy.anodyneQ.map f = (comparisonIso hcof hfib X).inv) :
    Nonempty (SSet.Homotopy (toReference hcof hfib X) f) :=
  (KanLocalizedRepresentatives.map_eq_iff_homotopy AnodyneHomotopy.anodyneQ
    (UniverseLift.horn_terminal_map (value_kan hcof hfib X)) _ _).mp
    ((toReference_map hcof hfib X).trans hf.symm)

def homEquiv (X Y : Cᵒᵖ × C) :
    HomotopyClasses.obj (value hcof hfib X) (value hcof hfib Y) ≃
      (AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) ⟶
        AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj Y)) :=
  (UniverseLift.smallLocalizedHomEquiv AnodyneHomotopy.anodyneQ _ _
    (value_kan hcof hfib Y)).trans
      (Iso.homCongr (comparisonIso hcof hfib X) (comparisonIso hcof hfib Y))

include hcof hfib in
lemma small_localizedHom (X Y : Cᵒᵖ × C) :
    Small.{v} (AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) ⟶
      AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj Y)) :=
  small_map (homEquiv hcof hfib X Y).symm

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference
