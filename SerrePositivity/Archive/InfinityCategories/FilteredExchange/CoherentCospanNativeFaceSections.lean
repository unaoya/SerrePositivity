module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleDiagramSections
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeSectionPullback

/-!
概要：元の左右の全三角形を、同じ native 切断族の各面と指定関手同型で比較する。
方針：一つの始点固定の全三角形比較を三面へ写し、図式側の面を元の二射影へ揃える。
規約：元の全三角形と指定比較を保持。使われ方：二脚・共通終点の同時移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)

local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection F) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 左三角形の指定比較を指定面の切断族へ写した同型。三面に同じ比較を用いる。 -/
def coherentCospanNativeLeftFaceSectionsIso (face : Fin 3) :=
  nativePointedTriangleFaceSectionsIso (face := face) c s hs el
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)

/-- 右三角形でも同じ全錐の制限と元の全三角形の指定比較を使用する。 -/
def coherentCospanNativeRightFaceSectionsIso (face : Fin 3) :=
  nativePointedTriangleFaceSectionsIso (face := face) c s hs er
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)

/-- 左三角形の図式側の切断族は、元の引き戻し比較の同じ左射影。 -/
lemma coherentCospanNativeLeftDiagramSections_eq :
    nativePointedTriangleDiagramSections c s hs el =
      coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.fst f g := by
  exact (nativePointedTriangleDiagramSections_eq c s hs el).trans
    (coherentCospanNativeSectionPullback_left F X Y Z C b).symm

/-- 右三角形の図式側でも、元の引き戻し比較の同じ右射影を回収する。 -/
lemma coherentCospanNativeRightDiagramSections_eq :
    nativePointedTriangleDiagramSections c s hs er =
      coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.snd f g := by
  exact (nativePointedTriangleDiagramSections_eq c s hs er).trans
    (coherentCospanNativeSectionPullback_right F X Y Z C b).symm

/-- 左の図式側の指定比較は、元の引き戻し比較の左射影と元の局所全族の間の同型。 -/
def coherentCospanNativeLeftDiagramSectionsIso :=
  let e := coherentCospanNativeLeftFaceSectionsIso F X Y Z C b 0
  let h := nativeConeTriangle_diagram_edge c el
  functorIsoOfEq
    (e.postcomp (eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) h)))
    (coherentCospanNativeLeftDiagramSections_eq F X Y Z C b) rfl

/-- 右の図式側の指定比較も、同じ元の引き戻し比較の右射影を持つ。 -/
def coherentCospanNativeRightDiagramSectionsIso :=
  let e := coherentCospanNativeRightFaceSectionsIso F X Y Z C b 0
  let h := nativeConeTriangle_diagram_edge c er
  functorIsoOfEq
    (e.postcomp (eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) h)))
    (coherentCospanNativeRightDiagramSections_eq F X Y Z C b) rfl

end SerrePositivity.InfinityCategories.F2
