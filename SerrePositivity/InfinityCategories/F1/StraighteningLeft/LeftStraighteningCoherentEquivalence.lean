module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningCoherentFullyFaithful
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：通常の圏の nerve 上で、実際の coherent straightening の分類同値を閉じる。
方針：小さい unstraightening の表現で同じ写像の本質的全射性を示し、F0 の判定を使う。
規約：単位・余単位の大域的な自然性や三角恒等式を仮定しない。
使われ方：任意の底の分類問題における、通常の nerve 上の比較の確定部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 通常の nerve 上の実際の分類写像は、小さい unstraightening の対象を回収する。 -/
def leftStraighteningCoherentCounitVertex {I : Type u} [SmallCategory I]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    VertexIso
      ((leftStraighteningCoherentMap I).app (Opposite.op ⦋0⦌)
        (leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F)))
      (functorVertex F) :=
  eqToIso (congrArg HomotopyCategory.mk
    (leftStraighteningCoherentMap_vertex (smallLeftUnstraighteningProjection F))) ≪≫
      nerveStraighteningRepresentationIso (smallLeftUnstraighteningProjection F)
        (smallUnstraighteningTransportRepresentation F)

/-- 通常の nerve 上の元の coherent straightening 写像は本質的全射。 -/
lemma leftStraighteningCoherentMap_isEssentiallySurjective
    (I : Type u) [SmallCategory I] :
    IsEssentiallySurjective (leftStraighteningCoherentMap I) := by
  intro v
  obtain ⟨F, rfl⟩ := (functorVertexEquiv _ _).surjective v
  exact ⟨leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F),
    ⟨leftStraighteningCoherentCounitVertex F⟩⟩

/-- 同じ実際の写像の充満忠実性と本質的全射性から、通常の nerve 上の分類同値を得る。 -/
lemma leftStraighteningCoherentMap_isQCatEquivalence (I : Type u) [SmallCategory I] :
    IsQCatEquivalence (leftStraighteningCoherentMap I) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (leftStraighteningCoherentMap_isFullyFaithful I)
    (leftStraighteningCoherentMap_isEssentiallySurjective I)

/-- 通常の nerve 上の分類同値。順方向は元の coherent straightening 写像。 -/
def leftStraighteningCoherentEquivalence (I : Type u) [SmallCategory I] :
    QCatEquivalence (LeftFibrationInfinity (nerve I))
      (SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))) :=
  (leftStraighteningCoherentMap_isQCatEquivalence I).choose

end SerrePositivity.InfinityCategories
