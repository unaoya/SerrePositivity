module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramBaseGroupNaturality

/-!
概要：任意の元の fiber 図式比較に対して、全整数接続射の自然性を証明する。
方針：同じ fiber・base 群同型で、指定 BF 区間の模型上の自然性を移送する。
規約：接続射の自然性を入力しない。使われ方：pro fiber 列の接続レベル射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

lemma fiberEquiv_map (j : ℤ) (x : NativeFiber.group D.triangle 0 0 j) :
    FiberPi.fiberEquiv (NativeFiber.rightMap E.triangle)
      (NativeFiber.asFiberSquare E.triangle E.isFiber) j
      (((SpectrumHo.piFunctor j).map ((vertex 0 0).map f)).hom x) =
    modelGroupMap f j (FiberPi.fiberEquiv (NativeFiber.rightMap D.triangle)
      (NativeFiber.asFiberSquare D.triangle D.isFiber) j x) :=
  ConcreteCategory.congr_hom (fiberGroupIso_naturality f j) x

lemma baseEquiv_map (j : ℤ) (x : NativeFiber.group D.triangle 1 1 j) :
    FiberPi.baseEquiv (NativeFiber.rightMap E.triangle)
      (NativeFiber.asFiberSquare E.triangle E.isFiber) j
      (((SpectrumHo.piFunctor j).map ((vertex 1 1).map f)).hom x) =
    homotopyMap (comparisonMap f 1 1) j
      (FiberPi.baseEquiv (NativeFiber.rightMap D.triangle)
        (NativeFiber.asFiberSquare D.triangle D.isFiber) j x) :=
  ConcreteCategory.congr_hom (baseGroupIso_naturality f j) x

lemma boundary_natural (j : ℤ) (x : NativeFiber.group D.triangle 1 1 (j + 1)) :
    ((SpectrumHo.piFunctor j).map ((vertex 0 0).map f)).hom
      (NativeFiber.boundary D.triangle D.isFiber j x) =
    NativeFiber.boundary E.triangle E.isFiber j
      (((SpectrumHo.piFunctor (j + 1)).map ((vertex 1 1).map f)).hom x) := by
  apply (fiberGroupIso E j).commGroupIsoToMulEquiv.injective
  change FiberPi.fiberEquiv (NativeFiber.rightMap E.triangle)
      (NativeFiber.asFiberSquare E.triangle E.isFiber) j
      (((SpectrumHo.piFunctor j).map ((vertex 0 0).map f)).hom
        (NativeFiber.boundary D.triangle D.isFiber j x)) =
    FiberPi.fiberEquiv (NativeFiber.rightMap E.triangle)
      (NativeFiber.asFiberSquare E.triangle E.isFiber) j
      (NativeFiber.boundary E.triangle E.isFiber j
        (((SpectrumHo.piFunctor (j + 1)).map ((vertex 1 1).map f)).hom x))
  rw [fiberEquiv_map]
  dsimp only [NativeFiber.boundary]
  have hD := FiberPi.boundary_equiv (NativeFiber.rightMap D.triangle)
    (NativeFiber.asFiberSquare D.triangle D.isFiber) j x
  have hE := FiberPi.boundary_equiv (NativeFiber.rightMap E.triangle)
    (NativeFiber.asFiberSquare E.triangle E.isFiber) j
    (((SpectrumHo.piFunctor (j + 1)).map ((vertex 1 1).map f)).hom x)
  have hB := baseEquiv_map f (j + 1) x
  exact (congrArg (modelGroupMap f j) hD).trans
    ((model_boundary_natural f j _).trans
      ((congrArg (homotopyFiberBoundary (NativeFiber.rightMap E.triangle) j) hB).symm.trans
        hE.symm))

lemma boundaryHom_natural (j : ℤ) :
    ((SpectrumHo.piFunctor j).map ((vertex 0 0).map f)).hom.comp
      (NativeFiber.boundary D.triangle D.isFiber j) =
    (NativeFiber.boundary E.triangle E.isFiber j).comp
      ((SpectrumHo.piFunctor (j + 1)).map ((vertex 1 1).map f)).hom := by
  ext x
  exact boundary_natural f j x

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
