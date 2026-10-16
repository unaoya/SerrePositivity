module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting

/-! # Homotopy extension with both specified endpoints along a localized mono

The entire original homotopy on the subobject is retained. Restriction
lifting is transported through the actual tensor/internal-Hom adjunction.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy
variable {A B K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hi hK in
lemma exists_extension (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    ∃ V : SSet.Homotopy f g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.boundary 1).ι
  have hr : HasLiftingProperty (SSet.boundary.{v} 1).ι
      ((CategoryTheory.MonoidalClosed.pre i).app K) :=
    KanRestrictionLifting.all_mono_rlp i hi hK _ inferInstance
  have hl : HasLiftingProperty pp.ι (terminal.from K) :=
    (CategoryTheory.MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff pp
      (Functor.PullbackObjObj.ofIsTerminal CategoryTheory.MonoidalClosed.internalHom
        i (terminal.from K) terminalIsTerminal)).mpr hr
  exact KanRelativeLifting.exists_extension i hl f g H

end SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy
