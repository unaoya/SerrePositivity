module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeUnderOverMap
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：元の二重 cone を、同じ終端 X 上の slice への大域 cone として構成する。
方針：元の恒等錐の下の全自然写像を uncurry し、全元単体の制限を回収する。
規約：元の全反対要素圏を使う。使われ方：大域二重 join と元の cone の比較。
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

def normalizedTensorDoubleConeOverJoin :
    join (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y)) ⟶
      sliceOver (normalizedTensorConePoint A X) :=
  sliceUnderUncurry (normalizedTensorDoubleConeUnderOverMap A X Y)

lemma normalizedTensorDoubleConeOverJoin_inl :
    joinInl (Δ[0] : SSet.{u + 1}) (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorDoubleConeOverJoin A X Y = normalizedTensorIdentityOverPoint A X :=
  sliceUnderUncurry_fixed (normalizedTensorDoubleConeUnderOverMap A X Y)

lemma normalizedTensorDoubleConeOverJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      normalizedTensorDoubleConeOverJoin A X Y =
      (pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := sliceOver (normalizedTensorConePoint A X))).symm
          (normalizedTensorDoubleConeOverSimplex A X Y c) := by
  rw [normalizedTensorDoubleConeOverJoin, ← sliceUnderUncurry_precomp,
    SSet.yonedaEquiv_symm_comp, normalizedTensorDoubleConeUnderOverMap_app,
    sliceUnderUncurry_yoneda]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
