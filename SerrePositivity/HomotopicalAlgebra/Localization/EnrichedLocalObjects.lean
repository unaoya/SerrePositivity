module

public import SerrePositivity.HomotopicalAlgebra.Localization.Enriched
public import SerrePositivity.HomotopicalAlgebra.Enriched.DerivedMapping

/-! # Ordinary local objects satisfy the actual V-valued derived Hom tests

Use the proved localized tensor model axiom and source Brown invariance
at the localized fibrant replacement. The source replacement and target
replacement in the V-valued tests are still the original specified data.
No unit or homotopy-generator condition on V is used in this direction.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [EnrichedOrdinaryCategory V C] [simplicial : ModelCategory SSet.{vC}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  (hP : @Quillen.IsQuillenBifunctor V _ base C _ m C _ m P.tensor)

include h hcof P hP in
lemma enrichedMappingTest_of_localEquivalence {X Z : C} (s : X ⟶ Z)
    (hs : (@localEquivalences C _ original simplicial cof fib S) s) (Y : C)
    (hY : @localObjects C _ original simplicial cof fib S Y) :
    let := original
    weakEquivalences V
      (((SerrePositivity.Enriched.derivedHom (V := V) cof fib).map s.op).app Y) := by
  let := original
  change weakEquivalences V
    (((SerrePositivity.Enriched.derivedHom (V := V) cof fib).map s.op).app Y)
  let Q := cofibrantSource cof
  let q := cofibrantSourceComparison cof
  let R := fibrantTarget fib
  have hRY : localObjects cof fib S (R.obj Y) :=
    (localObjects_iff_of_weakEquivalence cof fib hcof S ((fibrantTargetComparison fib).app Y)
      (fibrantTargetComparison_weakEquivalence fib Y)).mp hY
  have hRF : m.categoryWithFibrations.fibrations (terminal.from (R.obj Y)) :=
    (h.fibrant_iff _).mpr ⟨fibrantTarget_isFibrant fib Y, hRY⟩
  have hQs : localEquivalences cof fib S (Q.map s) := by
    intro W hW
    exact (mappingTest_arrow_iff cof fib hcof W
      (Arrow.homMk (q.app X) (q.app Z) (q.naturality s).symm)
      (cofibrantSourceComparison_trivialFibration cof X).2
      (cofibrantSourceComparison_trivialFibration cof Z).2).mpr
        (hs W hW)
  have hWs := h.weakEquivalences_eq.symm.le _ hQs
  let ix := initial.to (Q.obj X)
  let iz := initial.to (Q.obj Z)
  have hix : m.categoryWithCofibrations.cofibrations ix := h.cofibrations_eq.symm.le _
    ((cofibration_iff ix).mp (cofibrantSource_isCofibrant cof X))
  have hiz : m.categoryWithCofibrations.cofibrations iz := h.cofibrations_eq.symm.le _
    ((cofibration_iff iz).mp (cofibrantSource_isCofibrant cof Z))
  have hinit : IsInitial (⊥_ C) := initialIsInitial
  let := m
  have : Quillen.IsQuillenBifunctor P.tensor := hP
  have : Cofibration ix := ⟨hix⟩
  have : Cofibration iz := ⟨hiz⟩
  have : IsCofibrant (Q.obj X) := (isCofibrant_iff_of_isInitial ix hinit).mpr inferInstance
  have : IsCofibrant (Q.obj Z) := (isCofibrant_iff_of_isInitial iz hinit).mpr inferInstance
  have : IsFibrant (R.obj Y) := ⟨hRF⟩
  have := (SerrePositivity.Enriched.tensor_iff_mapping_model P).mp hP
  exact Quillen.pullbackHom_source_weakEquivalence P.tensorHom (Q.map s) hWs (R.obj Y)


include h hcof P hP in
lemma enrichedLocalObjects_of_localObjects (Y : C)
    (hY : @localObjects C _ original simplicial cof fib S Y) :
    let := original
    SerrePositivity.Enriched.localObjects (V := V) cof fib S Y := by
  let := original
  change SerrePositivity.Enriched.localObjects (V := V) cof fib S Y
  intro X Z s hs
  exact h.enrichedMappingTest_of_localEquivalence hcof P hP s
    (generators_le_localEquivalences cof fib S s hs) Y hY

end SerrePositivity.Bousfield.IsLocalizationModel
