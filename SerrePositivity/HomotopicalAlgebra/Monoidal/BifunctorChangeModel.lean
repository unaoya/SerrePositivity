module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.EndpointBifunctor

/-! # Changing the model in the acted-on variable of a Quillen bifunctor

Cofibrations are fixed and original weak equivalences remain weak.
Only the endpoint functors of generating cofibrations in the parameter
category need be left Quillen for the changed model. In particular, no
cofibrancy of generating domains in the acted-on category is required.
-/

@[expose] public section
universe wV wC vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
open SerrePositivity.ModelGeneration
variable {V : Type uV} [Category.{vV} V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  {m : ModelCategory C} {F : V ⥤ C ⥤ C}
  {G : Vᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ V}

lemma isQuillenBifunctor_change_second (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
    (hF : @IsQuillenBifunctor V _ base C _ original C _ original F)
    (hc : m.categoryWithCofibrations.cofibrations = original.categoryWithCofibrations.cofibrations)
    (hw : original.categoryWithWeakEquivalences.weakEquivalences ≤
      m.categoryWithWeakEquivalences.weakEquivalences)
    (IV JV : MorphismProperty V) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wV} IV JV]
    (IC JC : MorphismProperty C) [@_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wC} C _ m IC JC]
    (hend : ∀ {A B : V} (i : A ⟶ B), IV i →
      @IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
        m.categoryWithCofibrations m.categoryWithWeakEquivalences (F.obj A) ∧
      @IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
        m.categoryWithCofibrations m.categoryWithWeakEquivalences (F.obj B)) :
    @IsQuillenBifunctor V _ base C _ m C _ m F := by
  let := original
  have := hF
  have hcof {A B : V} (i : A ⟶ B) {X Y : C} (j : X ⟶ Y)
      (sq : F.PushoutObjObj i j) (hi : cofibrations V i)
      (hj : original.categoryWithCofibrations.cofibrations j) :
      original.categoryWithCofibrations.cofibrations sq.ι :=
    (cofibration_iff _).mp (hF.cofibration i j sq ⟨hi⟩ ⟨hj⟩)
  have hweak {A B : V} (i : A ⟶ B) {X Y : C} (j : X ⟶ Y)
      (sq : F.PushoutObjObj i j) (hi : trivialCofibrations V i)
      (hj : original.categoryWithCofibrations.cofibrations j) :
      original.categoryWithWeakEquivalences.weakEquivalences sq.ι :=
    (weakEquivalence_iff _).mp (hF.weakEquivalence i j sq ⟨hi.1⟩ ⟨hj⟩ (Or.inl ⟨hi.2⟩))
  let := m
  have hcof' {A B : V} (i : A ⟶ B) {X Y : C} (j : X ⟶ Y)
      (sq : F.PushoutObjObj i j) (hi : cofibrations V i) (hj : cofibrations C j) :
      cofibrations C sq.ι := hc.symm.le _ (hcof i j sq hi (hc.le j hj))
  have hiv : IV ≤ cofibrations V := IV.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated IV JV).symm.le
  have hjv : JV ≤ trivialCofibrations V :=
    JV.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated IV JV).symm.le
  have hic : IC ≤ cofibrations C := IC.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated IC JC).symm.le
  have hjc : JC ≤ trivialCofibrations C :=
    JC.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated IC JC).symm.le
  apply isQuillenBifunctor_of_generators adj adjFlip IV JV IC JC
  · intro A B i hi X Y j hj sq
    exact ⟨hcof' i j sq (hiv i hi) (hic j hj)⟩
  · intro A B i hi X Y j hj sq
    exact ⟨hcof' i j sq (hjv i hi).1 (hic j hj),
      hw _ (hweak i j sq (hjv i hi) (hc.le j (hic j hj)))⟩
  · intro A B i hi X Y j hj sq
    exact ⟨hcof' i j sq (hiv i hi) (hjc j hj).1,
      pushout_weakEquivalence_of_endpoint_functors F i (hend i hi).1 (hend i hi).2
        j (hjc j hj) sq⟩

end SerrePositivity.Quillen
