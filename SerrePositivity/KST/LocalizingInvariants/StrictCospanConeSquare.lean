module

public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeLegs

/-!
概要：通常の BF cospan の strict 錐を、同じ頂点・二射・二脚を持つ実正方形へ移す。
方針：cospan の horn 表示へ制限し、元の strict な錐の脚の計算と照合する。
規約：極限性の証人も移送する。使われ方：積射影の基底変換の実 pullback 正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (A B : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom A B) :=
  OmegaSpectrum.mappingSpace_kanComplex A B
variable {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
  (c : Cone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g))

def hornCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated) :=
  (DiagramLimitTransport.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
    CospanShape.strictCospanHornIso.inv).cast (CospanShape.strictDiagram_eq f g)

lemma hornCone_isLimit (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (hornCone f g c) := by
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have := DiagramLimitTransport.restriction_trivial
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g)) i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g)) i)
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (DiagramLimitTransport.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) i) :=
    (e.isTerminalVertex_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)).1 hc
  exact ht.cast (CospanShape.strictDiagram_eq f g)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (hornCone f g c)

lemma square_isPullback (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (square f g c) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (hornCone_isLimit f g c hc)

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square f g c =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
  rfl

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square f g c =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
  rfl

lemma square_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (square f g c) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c.pt := by
  rw [square, FiberModel.coneSquare_apex, hornCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast,
    DiagramLimitTransport.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]

end SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
