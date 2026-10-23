module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeDiagonalTransformation
public import SerrePositivity.InfinityCategories.F1.Joins.ConeTriangleTransformations
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleComposition

/-!
概要：元の錐の全 Hom の標準比較を、実際の unstraightening の相対合成と比較する。
方針：指定三角形の三辺を照合し、対角ホモトピーで元の標準比較へ戻す。
規約：元の錐・図式・全 Hom の全パラメータを保持する。
使われ方：定値始域の比較を通じて全切断の普遍性を検証する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の全 Hom の定値変換と、同じ指定錐の標準変換の実際の相対合成。 -/
def conePointHomRelativeComposite (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :=
  lift (conePointHomFirstTransformation c z ≫
      leftUnstraighteningMappingSpaceMap (SSet.const z) (SSet.const c.vertex : B ⟶ _))
    ((SSet.const (coneTransformationVertex c)) ≫
      leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F) ≫
    relativeFunctorComposition
      (Over.mk (leftUnstraighteningProjection (SSet.const z : B ⟶ _)))
      (Over.mk (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)))
      (Over.mk (leftUnstraighteningProjection F))

/-- 同じ指定三角形の長辺の像と二短辺の実際の相対合成の同型。 -/
def conePointHomTriangleComparisonIso (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso (coneDiagonalTransformation c z ≫
      leftUnstraighteningMappingSpaceMap (SSet.const z) F) (conePointHomRelativeComposite c z) :=
  F2.unstraighteningMappingTriangleIso (SSet.const z) (SSet.const c.vertex) F
    (conePointHomFirstTransformation c z) (SSet.const (coneTransformationVertex c))
    (coneDiagonalTransformation c z) (conePointHomTriangle c z)
    (conePointHomTriangle_first_transformation c z)
    (conePointHomTriangle_second_transformation c z)
    (conePointHomTriangle_diagonal_transformation c z)

/-- 元の native な全 Hom の錐族の標準比較と、同じ二変換の相対合成の同型。 -/
def conePointHomNativeCompositionIso (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso ((fixedApexConeHomComparison c z ≫ coneTransformationMap F z) ≫
      leftUnstraighteningMappingSpaceMap (SSet.const z) F)
      (conePointHomRelativeComposite c z) := by
  have e := functorIsoOfSimplicialHomotopy (coneDiagonalTransformationHomotopy c z)
  exact e.postcomp (leftUnstraighteningMappingSpaceMap (SSet.const z) F) ≪≫
    conePointHomTriangleComparisonIso c z

end SerrePositivity.InfinityCategories
