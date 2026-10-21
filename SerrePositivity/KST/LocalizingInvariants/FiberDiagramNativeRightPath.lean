module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightMappingPath
public import SerrePositivity.KST.LocalizingInvariants.SpectrumTrianglePathComparison

/-!
概要：元の右辺二三角形の相対 prism を保持した、新しい指定 BF 可換区間を構成する。
方針：各三角形の対角の全 Hom 類を BF で実現し、その実二辺の差の三角形を充填する。
規約：旧 rightMappingPath との一致は主張しない。使われ方：元の prism からの fiber 比較。
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

local instance nativeRightPathCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def nativeRightUpperRealization := SpectrumTriangleNormalization.pathRealization
  (comparisonMap f 1 0) (NativeFiber.rightMap E.triangle) (rightUpper f)
  ((rightUpper_two f).trans (comparisonMap_edge f 1 0).symm)
  ((rightUpper_zero f).trans (rightMap_edge E).symm)
  (rightDiagonalMap f) ((rightUpper_one f).trans (rightDiagonalMap_edge f).symm)

def nativeRightLowerRealization := SpectrumTriangleNormalization.pathRealization
  (NativeFiber.rightMap D.triangle) (comparisonMap f 1 1) (rightLower f)
  ((rightLower_two f).trans (rightMap_edge D).symm)
  ((rightLower_zero f).trans (comparisonMap_edge f 1 1).symm)
  (rightDiagonalMap f) ((rightLower_one f).trans (rightDiagonalMap_edge f).symm)

def nativeRightDifference := SpectrumMappingPrism.triangleDifference
  (nativeRightUpperRealization f).path (nativeRightLowerRealization f).path

def nativeRightMappingPath :
    (OmegaSpectrum.mappingSpace (SpectrumHo.spectrum ((vertex 1 0).obj D))
      (SpectrumHo.spectrum ((vertex 1 1).obj E))).Edge
        (OmegaSpectrum.vertexOfHom (comparisonMap f 1 0 ≫ NativeFiber.rightMap E.triangle))
        (OmegaSpectrum.vertexOfHom (NativeFiber.rightMap D.triangle ≫ comparisonMap f 1 1)) :=
  (nativeRightDifference f).edge

def nativeRightArrowTriangle := SpectrumMappingPath.arrowComposition
  (nativeRightDifference f).triangle

lemma nativeRightArrowHom_comp :
    SpectrumMappingPath.arrowHom (nativeRightUpperRealization f).path ≫
      SpectrumMappingPath.arrowHom (nativeRightMappingPath f) =
        SpectrumMappingPath.arrowHom (nativeRightLowerRealization f).path :=
  SpectrumMappingPath.arrowHom_comp (nativeRightDifference f).triangle

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
