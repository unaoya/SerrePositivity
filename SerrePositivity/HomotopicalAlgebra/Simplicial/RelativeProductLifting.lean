module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryTensorGluing

/-! # Relative lifting with arbitrary parameter shapes over a fixed base

Both the earlier parameter family and the entire prescribed subobject
family are retained. In particular, simplex boundaries of every dimension
may be filled while all degenerate inputs remain fixed. No model structure
or Kan condition on the source and base is required.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeProductLifting
variable {E B A X U V : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (i : A ⟶ X) [Mono i] (j : U ⟶ V) [Mono j]
  (earlier : X ⊗ U ⟶ E) (prescribed : A ⊗ V ⟶ E) (base : X ⊗ V ⟶ B)
  (hc : i ▷ U ≫ earlier = A ◁ j ≫ prescribed)
  (he : earlier ≫ p = X ◁ j ≫ base) (ha : prescribed ≫ p = i ▷ V ≫ base)

include hp hc he ha in
lemma exists_lift : ∃ f : X ⊗ V ⟶ E,
    X ◁ j ≫ f = earlier ∧ i ▷ V ≫ f = prescribed ∧ f ≫ p = base := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i j
  have : Mono (Arrow.mk i).hom := inferInstanceAs (Mono i)
  have : Mono (Arrow.mk j).hom := inferInstanceAs (Mono j)
  have : Mono pp.ι :=
    CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
      (X := Arrow.mk i) (Y := Arrow.mk j)
  have : HasLiftingProperty pp.ι p := hp _ inferInstance
  let b := pp.isPushout.desc earlier prescribed hc
  have hw : b ≫ p = pp.ι ≫ base := by
    apply pp.isPushout.hom_ext
    · dsimp only [b]
      rw [← Category.assoc, pp.isPushout.inl_desc, he, ← Category.assoc, pp.inl_ι]
      rfl
    · dsimp only [b]
      rw [← Category.assoc, pp.isPushout.inr_desc, ha, ← Category.assoc, pp.inr_ι]
      rfl
  let sq : CommSq b pp.ι p base := ⟨hw⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [show X ◁ j = pp.inl ≫ pp.ι from pp.inl_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  · rw [show i ▷ V = pp.inr ≫ pp.ι from pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _

def lift : X ⊗ V ⟶ E := (exists_lift p hp i j earlier prescribed base hc he ha).choose

lemma lift_earlier : X ◁ j ≫ lift p hp i j earlier prescribed base hc he ha = earlier :=
  (exists_lift p hp i j earlier prescribed base hc he ha).choose_spec.1

lemma lift_prescribed : i ▷ V ≫ lift p hp i j earlier prescribed base hc he ha = prescribed :=
  (exists_lift p hp i j earlier prescribed base hc he ha).choose_spec.2.1

lemma lift_base : lift p hp i j earlier prescribed base hc he ha ≫ p = base :=
  (exists_lift p hp i j earlier prescribed base hc he ha).choose_spec.2.2

end SerrePositivity.SimplicialModel.RelativeProductLifting
