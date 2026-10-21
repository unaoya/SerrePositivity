module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightMappingPath
public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalTriangle

/-!
概要：元の fiber 図式の右辺二三角形の差を、Sp の辺の関手圏の実三角形にする。
方針：指定した差の二単体を標準区間 Hom 比較で写し、全 h Fun の合成式を読む。
規約：比較や差の区間は選び直さない。使われ方：PathLift の prism と元の二三角形の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants
namespace SpectrumMappingPrism.TriangleDifference

local instance differenceArrowCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} {h f g : X ⟶ Y}
  {H : (mappingSpace X Y).Edge (vertexOfHom h) (vertexOfHom f)}
  {V : (mappingSpace X Y).Edge (vertexOfHom h) (vertexOfHom g)}
  (C : TriangleDifference H V)

def firstArrowHom (_C : TriangleDifference H V) := SpectrumMappingPath.arrowHom H

def longArrowHom (_C : TriangleDifference H V) := SpectrumMappingPath.arrowHom V

def arrowTriangle := SpectrumMappingPath.arrowComposition C.triangle

lemma arrowHom_comp : C.firstArrowHom ≫ SpectrumMappingPath.arrowHom C.edge =
    C.longArrowHom := SpectrumMappingPath.arrowHom_comp C.triangle

end SpectrumMappingPrism.TriangleDifference
namespace FiberDiagram

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def rightDifferenceArrowTriangle := (rightDifference f).arrowTriangle

def rightDifferenceUpperHom := (rightDifference f).firstArrowHom

def rightDifferenceLowerHom := (rightDifference f).longArrowHom

lemma rightDifferenceArrowHom_comp : rightDifferenceUpperHom f ≫
    SpectrumMappingPath.arrowHom (rightMappingPath f) = rightDifferenceLowerHom f :=
  (rightDifference f).arrowHom_comp

lemma rightDifferenceArrowTriangle_last :
    ((ihom (Δ[1] : SSet.{u + 1})).obj Sp.{u}).δ 0
      (rightDifferenceArrowTriangle f).simplex =
        (SpectrumMappingPath.arrowEdge (rightMappingPath f)).edge :=
  (rightDifferenceArrowTriangle f).d₀

end FiberDiagram
end SerrePositivity.KST.LocalizingInvariants
