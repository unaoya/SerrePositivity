module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-! # A model-free functorial mono factorization with a localized-equivalence right factor

Only the original boundary small-object argument is used. Every right
factor has an actual section and a vertical contraction, in the same
value universe. No Kan condition is imposed on the arrow's endpoints.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.MonoLocalizedFactorization

def factorization : MorphismProperty.FunctorialFactorizationData
    (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := by
  rw [← boundaryGenerators_leftClass]
  let : SSet.modelCategoryQuillen.I.{v}.HasSmallObjectArgument.{v} :=
    boundaryGenerators_smallObjectArgument
  exact MorphismProperty.functorialFactorizationData _ _

abbrev middle {A B : SSet.{v}} (f : A ⟶ B) : SSet.{v} := factorization.Z.obj (Arrow.mk f)
abbrev left {A B : SSet.{v}} (f : A ⟶ B) : A ⟶ middle f :=
  factorization.i.app (Arrow.mk f)
abbrev right {A B : SSet.{v}} (f : A ⟶ B) : middle f ⟶ B :=
  factorization.p.app (Arrow.mk f)

lemma fac {A B : SSet.{v}} (f : A ⟶ B) : left f ≫ right f = f :=
  factorization.fac_app

instance left_mono {A B : SSet.{v}} (f : A ⟶ B) : Mono (left f) := factorization.hi _

lemma right_all_mono_rlp {A B : SSet.{v}} (f : A ⟶ B) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (right f) := by
  rw [SSet.rlp_monomorphisms]
  exact factorization.hp _

lemma right_localized_isIso {A B : SSet.{v}} (f : A ⟶ B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (right f)) :=
  MonoRightLiftingContraction.localized_isIso _ (right_all_mono_rlp f)

lemma left_localized_isIso_iff {A B : SSet.{v}} (f : A ⟶ B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (left f)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (right f)) := right_localized_isIso f
  have he := congrArg AnodyneHomotopy.anodyneQ.map (fac f)
  rw [CategoryTheory.Functor.map_comp] at he
  rw [← he]
  exact (isIso_comp_right_iff (AnodyneHomotopy.anodyneQ.map (left f))
    (AnodyneHomotopy.anodyneQ.map (right f))).symm

end SerrePositivity.SimplicialModel.MonoLocalizedFactorization
