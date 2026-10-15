module

public import SerrePositivity.HomotopicalAlgebra.Localization.LocalReplacementDetection

/-! # Actual local replacement data and their homotopical properties

The unit, functor and local fibrant values are data. No strict idempotence
is imposed: the two natural maps into the double replacement are original
weak equivalences. All mapping tests retain the original model structure.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

structure LocalReplacementData (S : MorphismProperty C) where
  L : C ⥤ C
  η : 𝟭 C ⟶ L
  unit_cofibration (X : C) : cofibrations C (η.app X)
  unit_localEquivalence (X : C) : localEquivalences cof fib S (η.app X)
  localFibrant (X : C) : localFibrantObjects cof fib S (L.obj X)

namespace LocalReplacementData
variable {cof fib} {S : MorphismProperty C} (d : LocalReplacementData cof fib S)
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma detects_localEquivalences :
    localEquivalences cof fib S = (weakEquivalences C).inverseImage d.L :=
  localEquivalences_eq_inverseImage_of_localUnit cof fib hcof hfib S d.L d.η
    (fun X => (d.localFibrant X).2) d.unit_localEquivalence

include hcof hfib in
lemma map_mem_iff {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C (d.L.map f) ↔ localEquivalences cof fib S f :=
  (congrArg (fun P : MorphismProperty C => P f)
    (d.detects_localEquivalences hcof hfib)).symm.to_iff

include hcof hfib in
lemma map_weakEquivalence {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C (d.L.map f) :=
  (d.map_mem_iff hcof hfib f).mpr
    (weakEquivalences_le_localEquivalences cof fib hcof S f hf)

include hcof hfib in
lemma unit_weakEquivalence_of_local (X : C) (hX : localObjects cof fib S X) :
    weakEquivalences C (d.η.app X) :=
  (localEquivalence_iff_weakEquivalence_between_localObjects cof fib hcof hfib
    S (d.η.app X) hX (d.localFibrant X).2).mp (d.unit_localEquivalence X)

include hcof hfib in
lemma unit_weakEquivalence_iff_local (X : C) :
    weakEquivalences C (d.η.app X) ↔ localObjects cof fib S X := by
  constructor
  · intro h
    exact (localObjects_iff_of_weakEquivalence cof fib hcof S (d.η.app X) h).mpr
      (d.localFibrant X).2
  · exact d.unit_weakEquivalence_of_local hcof hfib X

include hcof hfib in
lemma unit_at_value_weakEquivalence (X : C) :
    weakEquivalences C (d.η.app (d.L.obj X)) :=
  d.unit_weakEquivalence_of_local hcof hfib _ (d.localFibrant X).2

include hcof hfib in
lemma map_unit_weakEquivalence (X : C) :
    weakEquivalences C (d.L.map (d.η.app X)) :=
  (d.map_mem_iff hcof hfib _).mpr (d.unit_localEquivalence X)

/-- The two maps into double replacement agree after precomposition with the unit. -/
lemma unit_naturality (X : C) :
    d.η.app X ≫ d.L.map (d.η.app X) = d.η.app X ≫ d.η.app (d.L.obj X) :=
  (d.η.naturality (d.η.app X)).symm

end LocalReplacementData
end SerrePositivity.Bousfield
