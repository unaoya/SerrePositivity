module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeDiagonalTransformation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransformation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTriangleFirst
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleComposition

/-!
概要：元の余錐の全 Hom の標準比較を、実際の unstraightening の相対合成と比較する。
方針：元の三角形の三辺を正規化し、対角のホモトピーで長辺を元の比較へ戻す。
規約：元の余錐と全 Hom の族を保持する。
使われ方：定値標的の fiber 表示へ移して全 Hom の普遍性を検証する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 概要：元の全 Hom の辺を定値図式間の変換として表示する。
方針：標準の左 Hom 区間比較を定値図式へ移す。
規約：元の底の全族。使われ方：相対合成の第二因子。 -/
def coconePointHomSecondTransformation (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :=
  constantDiagramTransformation B (pinchedHomLeftToIntervalMappingSpace c.vertex z)

/-- 概要：元の三角形の第二辺は指定した定値図式間の変換そのもの。
方針：底の標準区間比較の厳密な式を使う。
規約：全パラメータの式。使われ方：合成則への第二辺の入力。 -/
lemma coconePointHomTriangle_second_transformation
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z =
        coherentTransformationFamilyDiagram (coconePointHomSecondTransformation c z) := by
  rw [coconePointHomTriangle_second_standard, coconePointHomSecondTransformation,
    constantDiagramTransformation_diagram]

/-- 概要：元の余錐の変換の像と、全 Hom の定値変換の像の相対合成。
方針：実際の二つの比較射を同じパラメータで合成する。
規約：選択済みの比較射を用いる。使われ方：全 Hom の比較の合成側。 -/
def coconePointHomRelativeComposite (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :=
  lift ((SSet.const (coconeTransformationVertex c)) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const c.vertex))
    (coconePointHomSecondTransformation c z ≫
      leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) (SSet.const z : B ⟶ _)) ≫
    relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
      (Over.mk (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)))
      (Over.mk (leftUnstraighteningProjection (SSet.const z : B ⟶ _)))

/-- 概要：元の三角形の対角の像は元の二辺の実際の相対合成と同型。
方針：指定三角形上の全族の合成則に厳密な三辺を入力する。
規約：三角形を選び直さない。使われ方：元の全 Hom 比較への移送。 -/
def coconePointHomTriangleComparisonIso (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso (coconeDiagonalTransformation c z ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const z)) (coconePointHomRelativeComposite c z) :=
  unstraighteningMappingTriangleIso F (SSet.const c.vertex) (SSet.const z)
    (SSet.const (coconeTransformationVertex c)) (coconePointHomSecondTransformation c z)
    (coconeDiagonalTransformation c z) (coconePointHomTriangle c z)
    (coconePointHomTriangle_first_transformation c z)
    (coconePointHomTriangle_second_transformation c z)
    (coconePointHomTriangle_diagonal_transformation c z)

/-- 概要：元の全 Hom の余錐族の標準比較は実際の二つの比較の相対合成と同型。
方針：両端固定の対角ホモトピーを比較射で写し、指定三角形の合成同型と続ける。
規約：元の余錐と全 Hom の族。使われ方：定値標的の作用による余極限性の判定。 -/
def coconePointHomNativeCompositionIso (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso ((coconePointHomFamily c z ≫ coconeTransformationMap F z) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const z))
      (coconePointHomRelativeComposite c z) := by
  have e := functorIsoOfSimplicialHomotopy (coconeDiagonalTransformationHomotopy c z)
  exact (e.postcomp (leftUnstraighteningMappingSpaceMap F (SSet.const z))).symm ≪≫
    coconePointHomTriangleComparisonIso c z

end SerrePositivity.InfinityCategories.F2
