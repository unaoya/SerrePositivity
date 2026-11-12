module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightPrism
public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleDifference

/-!
概要：任意の fiber 図式比較の右辺 prism を、全 BF 写像空間の指定区間に移す。
方針：元の二三角形の六辺を復号し、その共通対角辺の差を外ホーンで取る。
規約：元の三角形の豊穣辺と差の実三角形を保持。使われ方：指定区間の相対持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance rightMappingSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

lemma comparisonMap_edge (i j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (comparisonMap f i j)).edge = (comparisonEdge f i j).edge :=
  SpectrumHo.edgeMap_edge _

def rightDiagonalMap := SpectrumHo.edgeMap (rightDiagonal f)

lemma rightDiagonalMap_edge : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (rightDiagonalMap f)).edge =
    (rightDiagonal f).edge := SpectrumHo.edgeMap_edge _

lemma rightMap_edge (A : FiberDiagram.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (NativeFiber.rightMap A.triangle)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow A.triangle.square).edge := SpectrumHo.edgeMap_edge _

def rightDifference := SpectrumMappingPrism.squareDifference
  (NativeFiber.rightMap D.triangle) (NativeFiber.rightMap E.triangle)
  (comparisonMap f 1 0) (comparisonMap f 1 1) (rightDiagonalMap f)
  (rightUpper f) (rightLower f)
  ((rightUpper_two f).trans (comparisonMap_edge f 1 0).symm)
  ((rightUpper_zero f).trans (rightMap_edge E).symm)
  ((rightUpper_one f).trans (rightDiagonalMap_edge f).symm)
  ((rightLower_two f).trans (rightMap_edge D).symm)
  ((rightLower_zero f).trans (comparisonMap_edge f 1 1).symm)
  ((rightLower_one f).trans (rightDiagonalMap_edge f).symm)

def rightMappingPath :
    (OmegaSpectrum.mappingSpace (SpectrumHo.spectrum ((vertex 1 0).obj D))
      (SpectrumHo.spectrum ((vertex 1 1).obj E))).Edge
        (OmegaSpectrum.vertexOfHom (comparisonMap f 1 0 ≫ NativeFiber.rightMap E.triangle))
        (OmegaSpectrum.vertexOfHom (NativeFiber.rightMap D.triangle ≫ comparisonMap f 1 1)) :=
  (rightDifference f).edge

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
