module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPostDetection
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-! # Internal Hom restriction along any localized equivalence is a localized equivalence

Neither a monomorphism nor a model structure is required.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanRestrictionEquivalence
variable {A B K : SSet.{v}} (a : A ⟶ B)
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include ha hK in
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map ((pre a).app K)) :=
  KanPostDetection.localized_isIso _ (SimplexParameterHom.native_kan B K hK)
    (SimplexParameterHom.native_kan A K hK)
    (KanRestrictionLifting.post_bijective a ha hK _).surjective
    (KanRestrictionLifting.post_bijective a ha hK _).injective

end SerrePositivity.SimplicialModel.KanRestrictionEquivalence
