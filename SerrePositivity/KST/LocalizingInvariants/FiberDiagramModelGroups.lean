module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramNativeRightPath
public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberInclusion

/-!
概要：任意の fiber 図式比較の右辺 prism が、元の右辺の BF fiber 群の実比較を誘導する。
方針：元の二三角形の相対 prism の対角を実現した BF 区間に、置換の群比較を適用する。
規約：元の fiber 頂点への移送は別工程。使われ方：その移送のための自然な模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

abbrev modelGroup (D : FiberDiagram.{u}) (j : ℤ) :=
  homotopyGroup (homotopyFiber (NativeFiber.rightMap D.triangle)) j

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def modelGroupMap (j : ℤ) : modelGroup D j →* modelGroup E j :=
  HomotopySquareGroups.groupMap (NativeFiber.rightMap D.triangle)
    (NativeFiber.rightMap E.triangle) (comparisonMap f 1 0) (comparisonMap f 1 1)
    (nativeRightMappingPath f) j

lemma model_boundary_natural (j : ℤ)
    (x : homotopyGroup (SpectrumHo.spectrum ((vertex 1 1).obj D)) (j + 1)) :
    modelGroupMap f j (homotopyFiberBoundary (NativeFiber.rightMap D.triangle) j x) =
      homotopyFiberBoundary (NativeFiber.rightMap E.triangle) j
        (homotopyMap (comparisonMap f 1 1) (j + 1) x) :=
  HomotopySquareGroups.boundary_natural _ _ _ _ _ j x

lemma model_inclusion_natural (j : ℤ) (x : modelGroup D j) :
    homotopyMap (homotopyFiberInclusion (NativeFiber.rightMap E.triangle)) j
        (modelGroupMap f j x) =
      homotopyMap (comparisonMap f 1 0) j
        (homotopyMap (homotopyFiberInclusion (NativeFiber.rightMap D.triangle)) j x) :=
  HomotopySquareGroups.inclusion_natural _ _ _ _ _ j x

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
