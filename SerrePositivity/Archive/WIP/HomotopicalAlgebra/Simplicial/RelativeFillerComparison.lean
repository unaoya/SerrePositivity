module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeProductLifting

/-! # Compare two whole fillers over their base and relative to both prescribed parts

Both the earlier parameter boundary and the entire input subobject stay
fixed throughout the comparison interval. The two fillers are retained.
The parameter shape is arbitrary and no model structure is required.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeFillerComparison
variable {E B A X U V : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (i : A ⟶ X) [Mono i] (j : U ⟶ V) [Mono j]
  (f g : X ⊗ V ⟶ E) (hbase : f ≫ p = g ≫ p)
  (he : X ◁ j ≫ f = X ◁ j ≫ g) (ha : i ▷ V ≫ f = i ▷ V ≫ g)

include hp hbase he ha in
lemma exists_comparison : ∃ H : SSet.Homotopy f g,
    H.h ≫ p = fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f ≫ p ∧
    (X ◁ j) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
      fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ (X ◁ j) ≫ f ∧
    (i ▷ V) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
      fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ (i ▷ V) ≫ f := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i j
  have : Mono (Arrow.mk i).hom := inferInstanceAs (Mono i)
  have : Mono (Arrow.mk j).hom := inferInstanceAs (Mono j)
  have : Mono pp.ι :=
    CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
      (X := Arrow.mk i) (Y := Arrow.mk j)
  have hfg : pp.ι ≫ f = pp.ι ≫ g := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.inl_ι]
      exact he
    · rw [← Category.assoc, pp.inr_ι]
      exact ha
  obtain ⟨H, hH, hr⟩ :=
    MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy p hp pp.ι f g hbase hfg
  refine ⟨H, hH, ?_, ?_⟩
  · rw [show X ◁ j = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      comp_whiskerRight, Category.assoc, hr, whiskerRight_fst_assoc]
  · rw [show i ▷ V = pp.inr ≫ pp.ι from pp.inr_ι.symm,
      comp_whiskerRight, Category.assoc, hr, whiskerRight_fst_assoc]

def comparison : SSet.Homotopy f g :=
  (exists_comparison p hp i j f g hbase he ha).choose

lemma comparison_base : (comparison p hp i j f g hbase he ha).h ≫ p =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f ≫ p :=
  (exists_comparison p hp i j f g hbase he ha).choose_spec.1

lemma comparison_earlier : (X ◁ j) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
    (comparison p hp i j f g hbase he ha).h =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ (X ◁ j) ≫ f :=
  (exists_comparison p hp i j f g hbase he ha).choose_spec.2.1

lemma comparison_prescribed : (i ▷ V) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
    (comparison p hp i j f g hbase he ha).h =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ (i ▷ V) ≫ f :=
  (exists_comparison p hp i j f g hbase he ha).choose_spec.2.2

end SerrePositivity.SimplicialModel.RelativeFillerComparison
