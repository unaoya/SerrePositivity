module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeOverProjection
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-!
概要：元の先端 X・全 frame 図式・終端 X を持つ実大域二重 join を構成する。
方針：同じ slice 内の大域 cone を uncurry し、前面・終端・両先端の恒等族を回収する。
規約：全元単体への制限も同じ実二重 cone を保つ。使われ方：元の augmentation 三角形。
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

def normalizedTensorDoubleConeJoin :
    join (join (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y))) Δ[0] ⟶
      dgNerve A (Complex A) := sliceOverUncurry (normalizedTensorDoubleConeOverJoin A X Y)

lemma normalizedTensorDoubleConeJoin_inl :
    joinInl (join (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y))) Δ[0] ≫
      normalizedTensorDoubleConeJoin A X Y = normalizedTensorConeJoin A X Y := by
  rw [normalizedTensorDoubleConeJoin, sliceOverUncurry_projection,
    normalizedTensorDoubleConeOverJoin_projection]

lemma normalizedTensorDoubleConeJoin_inr :
    joinInr (join (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y))) Δ[0] ≫
      normalizedTensorDoubleConeJoin A X Y = normalizedTensorConePoint A X :=
  sliceOverUncurry_fixed (normalizedTensorDoubleConeOverJoin A X Y)

lemma normalizedTensorDoubleConeJoin_endpoints :
    joinMap (joinInl (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y)))
      (𝟙 Δ[0]) ≫ normalizedTensorDoubleConeJoin A X Y =
      SSet.const ((dgNerve.vertexEquiv A (Complex A)).symm X) := by
  rw [normalizedTensorDoubleConeJoin, ← sliceOverUncurry_precomp,
    normalizedTensorDoubleConeOverJoin_inl, normalizedTensorIdentityOverPoint,
    InfinityCategories.sliceOverUncurry_yoneda]
  rfl

lemma normalizedTensorDoubleConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    joinMap (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c)) (𝟙 Δ[0]) ≫
      normalizedTensorDoubleConeJoin A X Y =
      joinMap (pointJoinStdSimplexIso n).hom (𝟙 Δ[0]) ≫
        (joinStdSimplexIso (n + 1) 0).hom ≫
          (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm
            (normalizedTensorDoubleConeSimplex A X Y c) := by
  rw [normalizedTensorDoubleConeJoin, ← sliceOverUncurry_precomp,
    normalizedTensorDoubleConeOverJoin_restrict_simplex, sliceOverUncurry_precomp,
    InfinityCategories.sliceOverUncurry_yoneda]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
