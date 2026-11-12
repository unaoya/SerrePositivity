module

public import SerrePositivity.KST.LocalizingInvariants.FiberPiComparison
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFiber

/-!
概要：同じ BF 射を右辺に持つ任意の Sp fiber 四角形の整数 π 長完全列。
方針：三対象の群同型で元の BF 接続射を共役し、三箇所の完全性を移す。
規約：下辺と右辺の作用は元の四角形を π 関手で写したもの。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberPi

local instance fiberExactSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {E B : OmegaSpectrum.{u}} (f : E ⟶ B)
  (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated)

abbrev fiberGroup (j : ℤ) := (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 0 0)
abbrev totalGroup (j : ℤ) := (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 1 0)
abbrev baseGroup (j : ℤ) := (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 1 1)

def bottom (j : ℤ) : fiberGroup f s j →* totalGroup f s j :=
  ((SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom s.square)).hom

def right (j : ℤ) : totalGroup f s j →* baseGroup f s j :=
  ((SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight s.square)).hom

def fiberEquiv (j : ℤ) : fiberGroup f s j ≃* homotopyGroup (homotopyFiber f) j :=
  (fiberGroupIso f s j).commGroupIsoToMulEquiv

def totalEquiv (j : ℤ) : totalGroup f s j ≃* homotopyGroup E j :=
  (totalGroupIso f s j).commGroupIsoToMulEquiv

def baseEquiv (j : ℤ) : baseGroup f s j ≃* homotopyGroup B j :=
  (baseGroupIso f s j).commGroupIsoToMulEquiv

/-- 同じ元の四角形の二辺に適合する接続準同型。 -/
def boundary (j : ℤ) : baseGroup f s (j + 1) →* fiberGroup f s j :=
  (fiberEquiv f s j).symm.toMonoidHom.comp
    ((homotopyFiberBoundary f j).comp (baseEquiv f s (j + 1)).toMonoidHom)

lemma bottom_equiv (j : ℤ) (a : fiberGroup f s j) :
    totalEquiv f s j (bottom f s j a) =
      homotopyMap (homotopyFiberInclusion f) j (fiberEquiv f s j a) :=
  ConcreteCategory.congr_hom (bottom_group_naturality f s j) a

lemma right_equiv (j : ℤ) (a : totalGroup f s j) :
    baseEquiv f s j (right f s j a) = homotopyMap f j (totalEquiv f s j a) :=
  ConcreteCategory.congr_hom (right_group_naturality f s j) a

lemma boundary_equiv (j : ℤ) (a : baseGroup f s (j + 1)) :
    fiberEquiv f s j (boundary f s j a) =
      homotopyFiberBoundary f j (baseEquiv f s (j + 1) a) :=
  (fiberEquiv f s j).apply_symm_apply _

lemma exact_fiber (j : ℤ) (a : fiberGroup f s j) :
    bottom f s j a = 1 ↔ ∃ b : baseGroup f s (j + 1), boundary f s j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (boundary f s j) (bottom f s j)
    (homotopyFiberBoundary f j) (homotopyMap (homotopyFiberInclusion f) j)
    (baseEquiv f s (j + 1)) (fiberEquiv f s j) (totalEquiv f s j)
    (boundary_equiv f s j) (bottom_equiv f s j) (homotopy_exact_connecting_fiber f j) a

lemma exact_total (j : ℤ) (a : totalGroup f s j) :
    right f s j a = 1 ↔ ∃ b : fiberGroup f s j, bottom f s j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (bottom f s j) (right f s j)
    (homotopyMap (homotopyFiberInclusion f) j) (homotopyMap f j)
    (fiberEquiv f s j) (totalEquiv f s j) (baseEquiv f s j)
    (bottom_equiv f s j) (right_equiv f s j) (homotopy_exact_fiber_total f j) a

lemma exact_base (j : ℤ) (a : baseGroup f s (j + 1)) :
    boundary f s j a = 1 ↔ ∃ b : totalGroup f s (j + 1), right f s (j + 1) b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (right f s (j + 1)) (boundary f s j)
    (homotopyMap f (j + 1)) (homotopyFiberBoundary f j)
    (totalEquiv f s (j + 1)) (baseEquiv f s (j + 1)) (fiberEquiv f s j)
    (right_equiv f s (j + 1)) (boundary_equiv f s j) (homotopy_exact_total_base f j) a

end SerrePositivity.KST.LocalizingInvariants.FiberPi
