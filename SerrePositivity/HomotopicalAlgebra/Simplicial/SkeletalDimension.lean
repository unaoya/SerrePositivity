module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! # The actual skeletal stage is the whole object in its dimension range -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SkeletalDimension
variable {A X : SSet.{v}} (i : A ⟶ X)

lemma eq_top (n : ℕ) [X.HasDimensionLT n] : SSet.skeletonOfMono i n = ⊤ := by
  rw [SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ n]
  intro d hd x _
  rw [SSet.skeletonOfMono_obj_eq_top i hd]
  trivial

def stageIso (n : ℕ) [X.HasDimensionLT n] :
    (SSet.skeletonOfMono i n).toSSet ≅ X :=
  SSet.Subcomplex.eqToIso (eq_top i n) ≪≫ SSet.Subcomplex.topIso X

end SerrePositivity.SimplicialModel.SkeletalDimension
