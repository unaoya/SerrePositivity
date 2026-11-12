module
public import SerrePositivity.KST.Fibration.DGRelativePiZero
public import SerrePositivity.KST.Fibration.DGKInputFiberSquare

/-! # 相対 Verdier 四角形の元の K 右辺の連結な実 fiber

右辺の fiber を構成する。元の四角形が引き戻しであることや、fiber が K(D) であることは未主張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

/-- 同じ元の相対四角形の K 右辺を持つ、構成済み Sp fiber 四角形。 -/
def dgRelativeFiberSquare : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.square ≫ dgKInputK A)) where
  square := (dgKInputFiberSquare A (dgRelativeRightArrowData A d).2.2).square
  zero_corner := (dgKInputFiberSquare A (dgRelativeRightArrowData A d).2.2).zero_corner
  right_edge := (dgKInputFiberSquare A (dgRelativeRightArrowData A d).2.2).right_edge.trans
    (congrArg SSet.yonedaEquiv.symm
      (congrArg ((dgKInputK A).app (Opposite.op ⦋1⦌)) (dgInputArrowData_edge A _)))
  isPullback := (dgKInputFiberSquare A (dgRelativeRightArrowData A d).2.2).isPullback

/-- 同じ相対 K 右辺の実 fiber の整数 π 群を、回収した同じ dg 射の BF fiber に比較する。 -/
def dgRelativeFiberPiComparison (j : ℤ) :
    (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (dgRelativeFiberSquare A d).square 0 0) ≅
      CommGrpCat.of (OmegaSpectrum.homotopyGroup
        (dgKBFHomotopyFiber A (dgRelativeRightArrowData A d).2.2) j) :=
  dgKInputFiberPiComparison A (dgRelativeRightArrowData A d).2.2 j

/-- 相対 Verdier 四角形の元の K 右辺の実 fiber は、全負整数 π 群が消える。 -/
theorem dgRelativeFiberSquare_negative_subsingleton (j : ℤ) (hj : j < 0) :
    Subsingleton ((SpectrumHo.piFunctor j).obj
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (dgRelativeFiberSquare A d).square 0 0)) := by
  have := dgKBFHomotopyFiber_negative_subsingleton_of_kZero_surjective A
    (dgRelativeRightArrowData A d).2.2 (dgRelativeRightArrow_kZero_surjective A d) j hj
  exact (dgRelativeFiberPiComparison A d j).commGroupIsoToMulEquiv.injective.subsingleton

end SerrePositivity.KST.Fibration
