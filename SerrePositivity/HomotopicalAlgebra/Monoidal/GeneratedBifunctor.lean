module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass

/-! # Quillen bifunctors checked on generating maps

Both ordinary parametrized adjoints are explicit. The three generator tests
extend by orthogonality, so no separate closure or cellular assumptions about
the pushout-product construction are needed.
-/

@[expose] public section
universe w₁ w₂ u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.Quillen
open SerrePositivity.ModelGeneration
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [ModelCategory C₁] [ModelCategory C₂] [ModelCategory C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} {H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁}

/-- The II, JI and IJ tests on the actual generators imply the full
two-variable Quillen condition for arbitrary pushout choices. -/
lemma isQuillenBifunctor_of_generators (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
    (I₁ J₁ : MorphismProperty C₁) (I₂ J₂ : MorphismProperty C₂)
    [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w₁} I₁ J₁] [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w₂} I₂ J₂]
    (hII : ∀ {A B : C₁} (i : A ⟶ B), I₁ i →
      ∀ {X Y : C₂} (j : X ⟶ Y), I₂ j → ∀ sq : F.PushoutObjObj i j, Cofibration sq.ι)
    (hJI : ∀ {A B : C₁} (i : A ⟶ B), J₁ i →
      ∀ {X Y : C₂} (j : X ⟶ Y), I₂ j → ∀ sq : F.PushoutObjObj i j,
        trivialCofibrations C₃ sq.ι)
    (hIJ : ∀ {A B : C₁} (i : A ⟶ B), I₁ i →
      ∀ {X Y : C₂} (j : X ⟶ Y), J₂ j → ∀ sq : F.PushoutObjObj i j,
        trivialCofibrations C₃ sq.ι) : IsQuillenBifunctor F := by
  constructor
  · intro A B X Y i j sq hi hj
    apply (cofibration_iff _).2
    rw [← trivialFibrations_llp]
    apply adj.pushout_generated_both adjFlip I₁ I₂ (trivialFibrations C₃) _ i _ j _ sq
    · intro A' B' i' hi' X' Y' j' hj' sq'
      rw [trivialFibrations_llp]
      exact (cofibration_iff _).1 (hII i' hi' j' hj' sq')
    · rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I₁ J₁]
      exact (cofibration_iff _).1 hi
    · rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I₂ J₂]
      exact (cofibration_iff _).1 hj
  · intro A B X Y i j sq hi hj hw
    have ht : trivialCofibrations C₃ sq.ι := by
      rw [← fibrations_llp]
      rcases hw with hiw | hjw
      · apply adj.pushout_generated_both adjFlip J₁ I₂ (fibrations C₃) _ i _ j _ sq
        · intro A' B' i' hi' X' Y' j' hj' sq'
          rw [fibrations_llp]
          exact hJI i' hi' j' hj' sq'
        · rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I₁ J₁]
          exact (mem_trivialCofibrations_iff _).2 ⟨hi, hiw⟩
        · rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I₂ J₂]
          exact (cofibration_iff _).1 hj
      · apply adj.pushout_generated_both adjFlip I₁ J₂ (fibrations C₃) _ i _ j _ sq
        · intro A' B' i' hi' X' Y' j' hj' sq'
          rw [fibrations_llp]
          exact hIJ i' hi' j' hj' sq'
        · rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I₁ J₁]
          exact (cofibration_iff _).1 hi
        · rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I₂ J₂]
          exact (mem_trivialCofibrations_iff _).2 ⟨hj, hjw⟩
    exact (weakEquivalence_iff _).2 ht.2

end SerrePositivity.Quillen
