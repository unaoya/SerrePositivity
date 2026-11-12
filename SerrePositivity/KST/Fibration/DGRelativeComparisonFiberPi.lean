module
public import SerrePositivity.KST.Fibration.DGRelativeFiberComparisonVertices
public import SerrePositivity.KST.Fibration.DGRelativeFiberSquare
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence

/-! # 同じ零角を持つ比較先 fiber の連結性と、非負次数への帰着

元の K(D) と比較先の実 fiber の負次数はともに消える。
残る条件は、構成した同じ比較辺の非負次数の π 作用である。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

local instance comparisonPiSpectrumCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 同じ canonical fiber 四角形を、回収した元の dg 右射の BF 表示で保持する。 -/
def dgRelativeCanonicalBFFiberSquare : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap A (dgRelativeRightArrowData A d).2.2)).toTruncated
    where
  square := (dgRelativeCanonicalFiberSquare A d).square
  zero_corner := (dgRelativeCanonicalFiberSquare A d).zero_corner
  right_edge := by
    have he : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.square ≫ dgKInputK A)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgKInputSpectrumMap A (dgRelativeRightArrowData A d).2.2)).edge :=
      (congrArg ((dgKInputK A).app (Opposite.op ⦋1⦌))
        (dgInputArrowData_edge A (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow d.square).edge)).symm.trans
          (dgKInputK_edge A (dgRelativeRightArrowData A d).2.2)
    exact (dgRelativeCanonicalFiberSquare A d).right_edge.trans
      (congrArg SSet.yonedaEquiv.symm he)
  isPullback := (dgRelativeCanonicalFiberSquare A d).isPullback

/-- 元の零角と右辺を持つ同じ fiber 頂点の π を、元の BF fiber と比較する。 -/
def dgRelativeCanonicalFiberPiComparison (j : ℤ) :
    (SpectrumHo.piFunctor j).obj
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (dgRelativeCanonicalFiberSquare A d).square 0 0) ≅
      CommGrpCat.of (OmegaSpectrum.homotopyGroup
        (dgKBFHomotopyFiber A (dgRelativeRightArrowData A d).2.2) j) :=
  FiberPi.fiberGroupIso (dgKInputSpectrumMap A (dgRelativeRightArrowData A d).2.2)
    (dgRelativeCanonicalBFFiberSquare A d) j

/-- 元の π₀ cofinality により、比較先の同じ実 fiber の全負次数は消える。 -/
theorem dgRelativeCanonicalFiber_negative_subsingleton (j : ℤ) (hj : j < 0) :
    Subsingleton ((SpectrumHo.piFunctor j).obj
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (dgRelativeCanonicalFiberSquare A d).square 0 0)) := by
  have := dgKBFHomotopyFiber_negative_subsingleton_of_kZero_surjective A
    (dgRelativeRightArrowData A d).2.2 (dgRelativeRightArrow_kZero_surjective A d) j hj
  exact (dgRelativeCanonicalFiberPiComparison A d j).commGroupIsoToMulEquiv.injective.subsingleton

/-- 比較元である元の K(D) 頂点も、同じ固定 K の負次数が消える。 -/
theorem dgRelativeKSource_negative_subsingleton (j : ℤ) (hj : j < 0) :
    Subsingleton ((SpectrumHo.piFunctor j).obj
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (d.square ≫ dgKInputK A) 0 0)) := by
  obtain ⟨P, hP⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (PerfDGInput.{u, v} A)).surjective
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 0)
  change Subsingleton ((SpectrumHo.piFunctor j).obj (HomotopyCategory.mk
    ((dgKInputK A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 0))))
  rw [← hP]
  exact dgKPi_negative_subsingleton A P j hj

/-- 構成した同じ比較辺の負次数の作用は、両端の消滅から全単射。 -/
theorem dgRelativeFiberComparison_pi_negative_bijective (j : ℤ) (hj : j < 0) :
    Function.Bijective (((SpectrumHo.piFunctor j).map
      (Truncated.HomotopyCategory.homMk
        (dgRelativeFiberVertexComparison A d).toTruncated)).hom) := by
  have : Subsingleton ((SpectrumHo.piFunctor j).obj
      (Truncated.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.square ≫ dgKInputK A) 0 0))) :=
    dgRelativeKSource_negative_subsingleton A d j hj
  have : Subsingleton ((SpectrumHo.piFunctor j).obj
      (Truncated.HomotopyCategory.mk (dgRelativeCanonicalFiberSquare A d).fiber)) :=
    dgRelativeCanonicalFiber_negative_subsingleton A d j hj
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨1, Subsingleton.elim _ _⟩⟩

/-- 残る非負次数の実比較が全単射なら、元の相対 K 四角形そのものは引き戻し。 -/
theorem dgRelativeK_isPullback_of_fiberComparison_pi_nonnegative
    (h : ∀ j : ℤ, 0 ≤ j → Function.Bijective (((SpectrumHo.piFunctor j).map
      (Truncated.HomotopyCategory.homMk
        (dgRelativeFiberVertexComparison A d).toTruncated)).hom)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ dgKInputK A) := by
  let e := dgRelativeFiberVertexComparison A d
  have hp : OmegaSpectrum.PiIsomorphism (SpectrumHo.edgeMap e) := by
    intro j
    have hb : Function.Bijective (((SpectrumHo.piFunctor j).map
        (Truncated.HomotopyCategory.homMk e.toTruncated)).hom) := by
      by_cases hj : j < 0
      · exact dgRelativeFiberComparison_pi_negative_bijective A d j hj
      · exact h j (by omega)
    change Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk e.toTruncated) j) at hb
    rw [SpectrumHo.piMap_edge] at hb
    exact hb
  apply (dgRelativeK_isPullback_iff_fiberVertexComparison_isInvertible A d).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (SpectrumHo.edgeMap_edge e)).mp
    (OmegaSpectrum.isInvertible_of_piIsomorphism _ hp)

end SerrePositivity.KST.Fibration
