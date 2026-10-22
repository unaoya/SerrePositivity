module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeProjection
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：元の全反対要素圏上の実 cone を、点とその nerve の join からの大域射として構成する。
方針：同じ coslice 写像を uncurry し、先端・通常図式・全単体への制限を厳密に回収する。
規約：同じ元の先端 X と全通常 frame 図式を保つ。使われ方：元の屋根との大域比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeJoin :
    join (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y)) ⟶
      dgNerve A (Complex A) := sliceUnderUncurry (normalizedTensorConeUnderMap A X Y)

lemma normalizedTensorConeJoin_inl :
    joinInl (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorConeJoin A X Y = normalizedTensorConePoint A X :=
  sliceUnderUncurry_fixed (normalizedTensorConeUnderMap A X Y)

lemma normalizedTensorConeJoin_inr :
    joinInr (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorConeJoin A X Y = normalizedTensorElementNerveDiagram A X Y := by
  rw [normalizedTensorConeJoin, sliceUnderUncurry_projection,
    normalizedTensorConeUnderMap_projection]

lemma normalizedTensorConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      normalizedTensorConeJoin A X Y =
      (pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm
          (normalizedTensorConeSimplex A X Y c) := by
  rw [normalizedTensorConeJoin, ← sliceUnderUncurry_precomp,
    SSet.yonedaEquiv_symm_comp, normalizedTensorConeUnderMap_app, sliceUnderUncurry_yoneda]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
