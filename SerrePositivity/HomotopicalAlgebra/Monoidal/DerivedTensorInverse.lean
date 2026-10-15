module

public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedWeakInverse
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor

/-! # Derived tensor invertibility from an actual weak evaluation

A weak map X tensor Y -> 1, with X, Y and the unit cofibrant, gives an
equivalence between tensoring by X and tensoring by Y on any ordinary
localization. The two natural composite comparisons are induced by the
actual evaluation and braiding, rather than assumed as inverse data.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def tensorEvaluationToIdentity {X Y : C} (e : X ⊗ Y ⟶ 𝟙_ C) :
    tensorLeft Y ⋙ tensorLeft X ⟶ 𝟭 C :=
  (tensorLeftTensor X Y).inv ≫ (tensoringLeft C).map e ≫ (leftUnitorNatIso C).hom

@[simp] lemma tensorEvaluationToIdentity_app {X Y : C} (e : X ⊗ Y ⟶ 𝟙_ C) (Z : C) :
    (tensorEvaluationToIdentity e).app Z = (α_ X Y Z).inv ≫ (e ▷ Z) ≫ (λ_ Z).hom := by
  simp [tensorEvaluationToIdentity]

variable [model : ModelCategory C] [BraidedCategory C] [MonoidalClosed C]
  [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
  {X Y : C} [IsCofibrant X] [IsCofibrant Y]

lemma tensorEvaluationToIdentity_weak (e : X ⊗ Y ⟶ 𝟙_ C) [WeakEquivalence e]
    (Z : C) [IsCofibrant Z] : WeakEquivalence ((tensorEvaluationToIdentity e).app Z) := by
  have := tensorRight_isLeftQuillen Z
  have := tensor_isCofibrant X Y
  have : WeakEquivalence ((tensorRight Z).map e) := map_weakEquivalence_of_cofibrant _ e
  rw [tensorEvaluationToIdentity_app]
  exact inferInstanceAs (WeakEquivalence ((α_ X Y Z).inv ≫ (tensorRight Z).map e ≫ (λ_ Z).hom))

variable {H : Type uH} [Category.{vH} H]
  (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]
  {LX LY : H ⥤ H}
  (α : Q ⋙ LX ⟶ tensorLeft X ⋙ Q) [LX.IsLeftDerivedFunctor α (weakEquivalences C)]
  (β : Q ⋙ LY ⟶ tensorLeft Y ⋙ Q) [LY.IsLeftDerivedFunctor β (weakEquivalences C)]

def derivedTensorInverseEquivalence (e : X ⊗ Y ⟶ 𝟙_ C) [WeakEquivalence e] : H ≌ H := by
  have := tensorLeft_isLeftQuillen X
  have := tensorLeft_isLeftQuillen Y
  have : WeakEquivalence ((β_ Y X).hom ≫ e) := inferInstance
  exact derivedWeakInverseEquivalence Q Q α β
    (tensorEvaluationToIdentity ((β_ Y X).hom ≫ e)) (tensorEvaluationToIdentity e)
    (fun Z _ ↦ tensorEvaluationToIdentity_weak _ Z)
    (fun Z _ ↦ tensorEvaluationToIdentity_weak _ Z)

include α β in
lemma derived_tensor_isEquivalence (e : X ⊗ Y ⟶ 𝟙_ C) [WeakEquivalence e] :
    LX.IsEquivalence := (derivedTensorInverseEquivalence Q α β e).isEquivalence_functor

end SerrePositivity.Quillen
