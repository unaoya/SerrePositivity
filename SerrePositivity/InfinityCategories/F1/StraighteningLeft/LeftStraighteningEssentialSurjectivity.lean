module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningRepresentation

/-!
概要：実際の coherent な straightening の本質的全射性。
方針：小さい unstraightening の標準表現を、実際の対象図式との比較へ適用する。
規約：余単位の成分を与える。全対象の自然性・充満忠実性・三角恒等式は別の工程。
使われ方：§5.6.5 の分類同値の本質的全射性の側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 実際の straightening は、小さい unstraightening から元の図式を関手同型で回収する。 -/
def leftStraighteningInfinityCounit {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    FunctorIso (leftStraighteningInfinityDiagram (smallLeftUnstraighteningProjection F)) F :=
  leftStraighteningInfinityDiagram_representationIso (smallLeftUnstraighteningProjection F)
    (smallUnstraighteningTransportRepresentation F)

/-- 実際の coherent な分類写像の余単位成分は、その対象の像の頂点を比較する。 -/
def leftStraighteningInfinityCounitVertex {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    VertexIso
      ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌)
        (leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F)))
      (functorVertex F) :=
  eqToIso (congrArg HomotopyCategory.mk
    (leftStraighteningInfinityDiagram_vertex (smallLeftUnstraighteningProjection F)).symm) ≪≫
      leftStraighteningInfinityCounit F

/-- 任意の小さい底で、実際の straightening 写像は本質的全射。 -/
lemma leftStraighteningInfinityMap_isEssentiallySurjective (B : SSet.{u}) :
    IsEssentiallySurjective (leftStraighteningInfinityMap B) := by
  intro v
  obtain ⟨F, rfl⟩ := (functorVertexEquiv _ _).surjective v
  exact ⟨leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F),
    ⟨leftStraighteningInfinityCounitVertex F⟩⟩

end SerrePositivity.InfinityCategories
