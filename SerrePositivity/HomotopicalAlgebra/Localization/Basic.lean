module

public import SerrePositivity.HomotopicalAlgebra.Localization.MappingTests
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison

/-! # Local objects and local equivalences from the constructed RMap

The only choices are explicit source/target model factorizations. These
definitions use the actual constructed simplicial Hom, not a placeholder
mapping-space oracle. No localized model structure is assumed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev mappingTest (Y : C) : MorphismProperty C :=
  MappingTests.test (chosenResolutionHom cof fib) (weakEquivalences SSet.{v}) Y

abbrev localObjects (S : MorphismProperty C) : C → Prop :=
  MappingTests.localObjects (chosenResolutionHom cof fib) (weakEquivalences SSet.{v}) S

abbrev localEquivalences (S : MorphismProperty C) : MorphismProperty C :=
  MappingTests.localEquivalences (chosenResolutionHom cof fib) (weakEquivalences SSet.{v}) S

def localFibrantObjects (S : MorphismProperty C) (Y : C) : Prop :=
  IsFibrant Y ∧ localObjects cof fib S Y

lemma generators_le_localEquivalences (S : MorphismProperty C) :
    S ≤ localEquivalences cof fib S := MappingTests.generators_le _ _ S

variable (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma weakEquivalences_le_mappingTest (Y : C) : weakEquivalences C ≤ mappingTest cof fib Y :=
  fun _ _ f hf => chosenResolutionHom_map_source_weakEquivalence hcof cof fib f.op hf Y

include hcof in
lemma weakEquivalences_le_localEquivalences (S : MorphismProperty C) :
    weakEquivalences C ≤ localEquivalences cof fib S :=
  fun _ _ f hf Y _ => weakEquivalences_le_mappingTest cof fib hcof Y f hf

include hcof in
lemma mappingTest_eq_of_target_weakEquivalence {Y Z : C} (q : Y ⟶ Z)
    (hq : weakEquivalences C q) : mappingTest cof fib Y = mappingTest cof fib Z :=
  MappingTests.test_eq_of_target _ _ q
    (fun X => chosenResolutionHom_map_target_weakEquivalence hcof cof fib X q hq)

include hcof in
lemma localObjects_iff_of_weakEquivalence (S : MorphismProperty C) {Y Z : C} (q : Y ⟶ Z)
    (hq : weakEquivalences C q) : localObjects cof fib S Y ↔ localObjects cof fib S Z := by
  change (S ≤ mappingTest cof fib Y) ↔ (S ≤ mappingTest cof fib Z)
  rw [mappingTest_eq_of_target_weakEquivalence cof fib hcof q hq]

include hcof in
lemma mappingTest_arrow_iff (Y : C) {X Z X' Z' : C} {f : X ⟶ Z} {g : X' ⟶ Z'}
    (a : Arrow.mk f ⟶ Arrow.mk g) (hl : weakEquivalences C a.left)
    (hr : weakEquivalences C a.right) :
    mappingTest cof fib Y f ↔ mappingTest cof fib Y g :=
  MappingTests.test_arrow_iff _ _ Y a
    (weakEquivalences_le_mappingTest cof fib hcof Y _ hl)
    (weakEquivalences_le_mappingTest cof fib hcof Y _ hr)

include hcof in
/-- Replacing the test maps by any naturally weakly equivalent representatives
preserves locality; in particular this applies to cofibrant replacement. -/
lemma localObjects_strictMap (S : MorphismProperty C) (Q : C ⥤ C)
    (q : Q ⟶ 𝟭 C) (hq : ∀ X, weakEquivalences C (q.app X)) (Y : C) :
    localObjects cof fib (S.strictMap Q) Y ↔ localObjects cof fib S Y := by
  have ht {X Z : C} (f : X ⟶ Z) :
      mappingTest cof fib Y (Q.map f) ↔ mappingTest cof fib Y f :=
    mappingTest_arrow_iff cof fib hcof Y (Arrow.homMk (q.app X) (q.app Z)
      (q.naturality f).symm) (hq X) (hq Z)
  constructor
  · intro h X Z f hf
    exact (ht f).mp (h (Q.map f) (.map hf))
  · intro h X Z f hf
    cases hf with
    | @map X Z f hf => exact (ht f).mpr (h f hf)

include hcof in
/-- The definition testing all local targets equals the conventional definition
testing only fibrant local targets, because RMap already derives its target. -/
lemma localEquivalences_iff_fibrant (S : MorphismProperty C) {X Z : C} (f : X ⟶ Z) :
    localEquivalences cof fib S f ↔
      ∀ Y, localFibrantObjects cof fib S Y → mappingTest cof fib Y f := by
  constructor
  · exact fun h Y hY => h Y hY.2
  · intro h Y hY
    let R := fibrantTarget fib
    let q := (fibrantTargetComparison fib).app Y
    have hq := fibrantTargetComparison_weakEquivalence fib Y
    have hlocal := (localObjects_iff_of_weakEquivalence cof fib hcof S q hq).mp hY
    have ht := mappingTest_eq_of_target_weakEquivalence cof fib hcof q hq
    exact (congrArg (fun P : MorphismProperty C => P f) ht).mpr
      (h (R.obj Y) ⟨fibrantTarget_isFibrant fib Y, hlocal⟩)

include hcof in
lemma localObjects_of_le_weakEquivalences {S : MorphismProperty C}
    (hS : S ≤ weakEquivalences C) (Y : C) : localObjects cof fib S Y :=
  hS.trans (weakEquivalences_le_mappingTest cof fib hcof Y)

include hcof in
/-- Adding maps that were already original weak equivalences changes neither
the local objects nor their detected equivalences. -/
lemma localObjects_sup_weakEquivalences (S : MorphismProperty C) :
    localObjects cof fib (S ⊔ weakEquivalences C) = localObjects cof fib S := by
  funext Y
  apply propext
  exact ⟨fun h => le_sup_left.trans h,
    fun h => sup_le h (weakEquivalences_le_mappingTest cof fib hcof Y)⟩

include hcof in
lemma localEquivalences_sup_weakEquivalences (S : MorphismProperty C) :
    localEquivalences cof fib (S ⊔ weakEquivalences C) = localEquivalences cof fib S := by
  ext X Z f
  change (∀ Y, localObjects cof fib (S ⊔ weakEquivalences C) Y → _) ↔ _
  rw [localObjects_sup_weakEquivalences cof fib hcof S]
  rfl

end SerrePositivity.Bousfield
