module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.GeneratedBifunctor

/-! # Pushout-product compatibility from Quillen functors at generator endpoints

The weak-equivalence part of a pushout-product follows by cobase change
and two-out-of-three when the two endpoint functors are left Quillen.
It suffices to check these endpoint functors at the generating
cofibrations in each variable. No condition on the endpoints of the
generating trivial cofibrations is required.
-/

@[expose] public section
universe w₁ w₂ u₁ v₁ u₂ v₂ u₃ v₃
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
open SerrePositivity.ModelGeneration
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [ModelCategory C₁] [ModelCategory C₂] [ModelCategory C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃)

omit [ModelCategory C₁] in
lemma pushout_weakEquivalence_of_endpoint_functors {A B : C₁} (i : A ⟶ B)
    (hA : IsLeftQuillen (F.obj A)) (hB : IsLeftQuillen (F.obj B))
    {X Y : C₂} (j : X ⟶ Y) (hj : trivialCofibrations C₂ j) (sq : F.PushoutObjObj i j) :
    weakEquivalences C₃ sq.ι := by
  have ha := hA.map_trivialCofibrations j hj
  have hb := hB.map_trivialCofibrations j hj
  have hl : trivialCofibrations C₃ sq.inl :=
    (trivialCofibrations C₃).of_isPushout sq.isPushout ha
  exact (weakEquivalences C₃).of_precomp _ _ hl.2 (sq.inl_ι.symm ▸ hb.2)

variable {F} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} {H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁}

lemma isQuillenBifunctor_of_generator_endpoints (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
    (I₁ J₁ : MorphismProperty C₁) (I₂ J₂ : MorphismProperty C₂)
    [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w₁} I₁ J₁] [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w₂} I₂ J₂]
    (hc : ∀ {A B : C₁} (i : A ⟶ B) {X Y : C₂} (j : X ⟶ Y)
      (sq : F.PushoutObjObj i j), Cofibration i → Cofibration j → Cofibration sq.ι)
    (hI₁ : ∀ {A B : C₁} (i : A ⟶ B), I₁ i →
      IsLeftQuillen (F.obj A) ∧ IsLeftQuillen (F.obj B))
    (hI₂ : ∀ {X Y : C₂} (j : X ⟶ Y), I₂ j →
      IsLeftQuillen (F.flip.obj X) ∧ IsLeftQuillen (F.flip.obj Y)) : IsQuillenBifunctor F := by
  have hi₁ : I₁ ≤ cofibrations C₁ :=
    I₁.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I₁ J₁).symm.le
  have hi₂ : I₂ ≤ cofibrations C₂ :=
    I₂.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I₂ J₂).symm.le
  have hj₁ : J₁ ≤ trivialCofibrations C₁ :=
    J₁.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I₁ J₁).symm.le
  have hj₂ : J₂ ≤ trivialCofibrations C₂ :=
    J₂.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I₂ J₂).symm.le
  apply isQuillenBifunctor_of_generators adj adjFlip I₁ J₁ I₂ J₂
  · intro A B i hi X Y j hj sq
    exact hc i j sq ⟨hi₁ i hi⟩ ⟨hi₂ j hj⟩
  · intro A B i hi X Y j hj sq
    have hjC : Cofibration j := ⟨hi₂ j hj⟩
    have hiC : Cofibration i := ⟨(hj₁ i hi).1⟩
    exact ⟨(cofibration_iff _).mp (hc i j sq hiC hjC),
      pushout_weakEquivalence_of_endpoint_functors F.flip j (hI₂ j hj).1 (hI₂ j hj).2
        i (hj₁ i hi) sq.flip⟩
  · intro A B i hi X Y j hj sq
    have hiC : Cofibration i := ⟨hi₁ i hi⟩
    have hjC : Cofibration j := ⟨(hj₂ j hj).1⟩
    exact ⟨(cofibration_iff _).mp (hc i j sq hiC hjC),
      pushout_weakEquivalence_of_endpoint_functors F i (hI₁ i hi).1 (hI₁ i hi).2
        j (hj₂ j hj) sq⟩

end SerrePositivity.Quillen
