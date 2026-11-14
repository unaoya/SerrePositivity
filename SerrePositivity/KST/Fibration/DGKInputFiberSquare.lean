module
public import SerrePositivity.KST.Fibration.DGKFiberConnectivity
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquareArrows

/-! # 固定 K の元の実辺を右辺に持つ Sp fiber 四角形と、その連結性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

local instance : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory
variable (A : Type u) [CommRing A]

/-- 元の BF fiber 四角形を、その同じ固定 K 辺の表示で保持する。 -/
def dgKInputFiberSquare {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated) where
  square := (FiberModel.homotopyFiberSquare (dgKInputSpectrumMap A f)).square
  zero_corner := (FiberModel.homotopyFiberSquare (dgKInputSpectrumMap A f)).zero_corner
  right_edge := (FiberModel.homotopyFiberSquare (dgKInputSpectrumMap A f)).right_edge.trans
    (congrArg SSet.yonedaEquiv.symm (dgKInputK_edge A f).symm)
  isPullback := (FiberModel.homotopyFiberSquare (dgKInputSpectrumMap A f)).isPullback

/-- 同じ Sp fiber 頂点の整数 π 群は、元の実 BF homotopy fiber の同じ群と同型。 -/
def dgKInputFiberPiComparison {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) (j : ℤ) :
    (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (dgKInputFiberSquare A f).square 0 0) ≅
      CommGrpCat.of (OmegaSpectrum.homotopyGroup (dgKBFHomotopyFiber A f) j) :=
  (SpectrumHo.piFunctor j).mapIso (FiberModel.fiberObjectIso (dgKInputSpectrumMap A f)) ≪≫
    SpectrumHo.piComparison (dgKBFHomotopyFiber A f) j

/-- ν 像が Verdier 列なら、元の固定 K 商辺の実 Sp fiber 頂点は全負整数群が消える。 -/
theorem dgKInputFiberSquare_negative_subsingleton_of_verdier
    {P Q R : PerfDGInput.{u, v} A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A P) (dgKInputStableValue A Q) from dgKInputNuMap A f)
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A Q) (dgKInputStableValue A R) from dgKInputNuMap A g))
    (j : ℤ) (hj : j < 0) :
    Subsingleton ((SpectrumHo.piFunctor j).obj
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (dgKInputFiberSquare A g).square 0 0)) := by
  have := dgKBFHomotopyFiber_negative_subsingleton_of_verdier A f g h j hj
  exact (dgKInputFiberPiComparison A g j).commGroupIsoToMulEquiv.injective.subsingleton

end SerrePositivity.KST.Fibration
