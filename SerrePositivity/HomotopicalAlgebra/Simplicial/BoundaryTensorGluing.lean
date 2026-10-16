module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-! # Gluing actual whole tensor-parameter families along a simplicial boundary -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BoundaryTensorGluing
variable {T P : SSet.{v}}

abbrev Compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    T ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ faces j =
      T ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ faces k

lemma curry_compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : Compatible faces) : BoundaryGluing.StandardCompatible (fun k => curry (faces k)) := by
  intro j k hjk
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
  exact hf j k hjk

def desc {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : Compatible faces) : T ⊗ (SSet.boundary (n + 2)).toSSet ⟶ P :=
  uncurry (BoundaryGluing.standardDesc (fun k => curry (faces k)) (curry_compatible faces hf))

@[reassoc]
lemma desc_fac {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : Compatible faces) (k : Fin (n + 3)) :
    T ◁ SSet.boundary.ι k ≫ desc faces hf = faces k := by
  rw [desc, ← uncurry_natural_left, BoundaryGluing.standardDesc_fac, uncurry_curry]

lemma hom_ext {n : ℕ} {f g : T ⊗ (SSet.boundary (n + 1)).toSSet ⟶ P}
    (h : ∀ k : Fin (n + 2), T ◁ SSet.boundary.ι k ≫ f = T ◁ SSet.boundary.ι k ≫ g) :
    f = g := by
  have hc : curry f = curry g := by
    apply SSet.boundary.hom_ext
    intro k
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact h k
  exact (uncurry_curry f).symm.trans ((congrArg uncurry hc).trans (uncurry_curry g))

end SerrePositivity.SimplicialModel.BoundaryTensorGluing
