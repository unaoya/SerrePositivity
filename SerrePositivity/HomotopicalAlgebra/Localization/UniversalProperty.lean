module

public import SerrePositivity.HomotopicalAlgebra.Localization.QuillenCriterion
public import SerrePositivity.HomotopicalAlgebra.Localization.QuillenLocalObjects
public import SerrePositivity.HomotopicalAlgebra.Localization.ModelComparison
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedMapTest

/-! # Quillen universal property of an actual left Bousfield localization

An original Quillen adjunction extends precisely when the left adjoint
sends the specified cofibrant approximation of every test map to a weak
equivalence. Arbitrary original test maps are allowed. The proof uses the
fibrant right-adjoint criterion and actual resolution Hom adjunction.
-/

@[expose] public section
universe vC uC vD uD vHC uHC vHD uHD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{vC}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  {D : Type uD} [Category.{vD} D] [target : ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (hF : @Quillen.IsLeftQuillen C _ D _ original.categoryWithCofibrations
    original.categoryWithWeakEquivalences target.categoryWithCofibrations
    target.categoryWithWeakEquivalences L)
  [ModelCategory SSet.{vD}] [ModelCategory SSet.{max vC vD}]
  (hcofD : cofibrations SSet.{vD} = MorphismProperty.monomorphisms _)
  (hfibD : fibrations SSet.{vD} = SSet.modelCategoryQuillen.J.{vD}.rlp)
  (hcofB : cofibrations SSet.{max vC vD} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vD} = SSet.modelCategoryQuillen.J.{max vC vD}.rlp)

include h hcof hfib adj hF hcofD hfibD hcofB hfibB in
lemma leftQuillen_iff_cofibrant_test :
    @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences target.categoryWithCofibrations
      target.categoryWithWeakEquivalences L ↔
    ∀ {X Z : C} (f : X ⟶ Z), S f → weakEquivalences D
      (L.map (((@HomotopyFunctionComplex.cofibrantSource C _ original cof)).map f)) := by
  let := original
  constructor
  · intro hn X Z f hf
    let Q := (@HomotopyFunctionComplex.cofibrantSource C _ original cof)
    let q := HomotopyFunctionComplex.cofibrantSourceComparison cof
    have hQ : localEquivalences.{vC, uC} (C := C) cof fib S (Q.map f) := by
      intro Y hY
      exact (mappingTest_arrow_iff cof fib hcof Y
        (Arrow.homMk (q.app X) (q.app Z) (q.naturality f).symm)
        (HomotopyFunctionComplex.cofibrantSourceComparison_trivialFibration cof X).2
        (HomotopyFunctionComplex.cofibrantSourceComparison_trivialFibration cof Z).2).mpr
          (generators_le_localEquivalences cof fib S f hf Y hY)
    have hW := h.weakEquivalences_eq.symm.le _ hQ
    let ix := initial.to (Q.obj X)
    let iz := initial.to (Q.obj Z)
    have hix : m.categoryWithCofibrations.cofibrations ix := h.cofibrations_eq.symm.le _
      ((cofibration_iff ix).mp (HomotopyFunctionComplex.cofibrantSource_isCofibrant cof X))
    have hiz : m.categoryWithCofibrations.cofibrations iz := h.cofibrations_eq.symm.le _
      ((cofibration_iff iz).mp (HomotopyFunctionComplex.cofibrantSource_isCofibrant cof Z))
    have hinit : IsInitial (⊥_ C) := initialIsInitial
    let := m
    have : Quillen.IsLeftQuillen L := hn
    have : Cofibration ix := ⟨hix⟩
    have : Cofibration iz := ⟨hiz⟩
    have : IsCofibrant (Q.obj X) := (isCofibrant_iff_of_isInitial ix hinit).mpr inferInstance
    have : IsCofibrant (Q.obj Z) := (isCofibrant_iff_of_isInitial iz hinit).mpr inferInstance
    have : WeakEquivalence (Q.map f) := ⟨hW⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L (Q.map f))
  · intro hS
    have := hF
    apply (h.leftQuillen_iff_rightAdjoint_local hcof hfib adj hF).mpr
    intro Y hY
    have : IsFibrant Y := hY
    exact rightAdjoint_local_of_cofibrant_test adj cof fib hcof hfib hcofD hfibD
      hcofB hfibB S hS Y


include h hcof hfib adj hF hcofD hfibD hcofB hfibB in
lemma cofibrant_test_choices_iff
    (cof' : MorphismProperty.FunctorialFactorizationData
      original.categoryWithCofibrations.cofibrations
      (original.categoryWithFibrations.fibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences))
    (fib' : MorphismProperty.FunctorialFactorizationData
      (original.categoryWithCofibrations.cofibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences)
      original.categoryWithFibrations.fibrations) :
    let := original
    (∀ {X Z : C} (f : X ⟶ Z), S f → weakEquivalences D
      (L.map ((HomotopyFunctionComplex.cofibrantSource cof).map f))) ↔
    (∀ {X Z : C} (f : X ⟶ Z), S f → weakEquivalences D
      (L.map ((HomotopyFunctionComplex.cofibrantSource cof').map f))) := by
  let := original
  have h' := h.changeChoices cof' fib' hcof
  exact (h.leftQuillen_iff_cofibrant_test hcof hfib adj hF hcofD hfibD hcofB hfibB).symm.trans
    (h'.leftQuillen_iff_cofibrant_test hcof hfib adj hF hcofD hfibD hcofB hfibB)


variable {HC : Type uHC} [Category.{vHC} HC] {HD : Type uHD} [Category.{vHD} HD]
  (QC : C ⥤ HC) [hQC : QC.IsLocalization original.categoryWithWeakEquivalences.weakEquivalences]
  (QD : D ⥤ HD) [hQD : QD.IsLocalization (weakEquivalences D)]
  {LF : HC ⥤ HD} (α : QC ⋙ LF ⟶ L ⋙ QD)
  [hLF : LF.IsLeftDerivedFunctor α original.categoryWithWeakEquivalences.weakEquivalences]

include h hcof hfib adj hF hcofD hfibD hcofB hfibB QC QD α hQC hQD hLF in
lemma leftQuillen_iff_derived_inverts :
    @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences target.categoryWithCofibrations
      target.categoryWithWeakEquivalences L ↔
    ∀ {X Z : C} (f : X ⟶ Z), S f → IsIso (LF.map (QC.map f)) := by
  let := original
  have := hF
  refine (h.leftQuillen_iff_cofibrant_test hcof hfib adj hF hcofD hfibD hcofB hfibB).trans ?_
  constructor
  · intro hS X Z f hf
    exact (@Quillen.derived_map_isIso_iff_cofibrant_image C _ original D _ target HC _ HD _
      QC hQC QD hQD L hF LF α hLF cof X Z f).mpr (hS f hf)
  · intro hS X Z f hf
    exact (@Quillen.derived_map_isIso_iff_cofibrant_image C _ original D _ target HC _ HD _
      QC hQC QD hQD L hF LF α hLF cof X Z f).mp (hS f hf)

end SerrePositivity.Bousfield.IsLocalizationModel
