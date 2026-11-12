module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierReflectiveCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientShiftReflective

/-!
概要：充満忠実右随伴の場合の一般商の実 pullback を、元の p・q の実 pullback へ比較する。
方針：元の cofiber 差の Verdier 列を代入し、二脚の全関手同型を境界変形へ移す。
規約：既存の Tamme fiber 列と同じ入力を使う。使われ方：d8 と Tamme Prop. 11・Cor. 12。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.TammePullback
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (adj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

def original : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  LaxQuotientPullback.square hΦ p q (pullbackInclusion p q) (exactLaxDifference p q)
    (laxDifference_isVerdier p q v adj hv)

def oldFrame : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.cSource (Φ := Φ) p q (pullbackInclusion p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.dLeg (Φ := Φ) p q (exactLaxDifference p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.dSource (Φ := Φ) p q (pullbackInclusion p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.cLeg (Φ := Φ) p q (exactLaxDifference p q)))

lemma oldFrame_eq : oldFrame (Φ := Φ) p q = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (original hΦ p q v adj hv) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ext
  · exact (LaxQuotientPullback.square_bottom hΦ p q _ _ _).symm
  · exact (LaxQuotientPullback.square_top hΦ p q _ _ _).symm
  · exact (LaxQuotientPullback.square_left hΦ p q _ _ _).symm
  · exact (LaxQuotientPullback.square_right hΦ p q _ _ _).symm

def newFrame : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.cSource (Φ := Φ) p q (pullbackInclusion p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ q))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.dSource (Φ := Φ) p q (pullbackInclusion p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ p))

def boundaryHomotopy : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (oldFrame (Φ := Φ) p q) (newFrame (Φ := Φ) p q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy _ _ _ _ _ _ _ _ rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.valueMap_laxQuotientDLeg_cofiber p q Φ) rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.valueMap_laxQuotientCLeg_cofiber p q Φ)

def extension : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.pathFrame (boundaryHomotopy (Φ := Φ) p q))
    (original hΦ p q v adj hv) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension (boundaryHomotopy (Φ := Φ) p q)) _ (oldFrame_eq hΦ p q v adj hv)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (extension hΦ p q v adj hv).target

def comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (original hΦ p q v adj hv) (square hΦ p q v adj hv) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.comparison (extension hΦ p q v adj hv))

lemma square_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (square hΦ p q v adj hv) :=
  (LaxQuotientPullback.square_isPullback hΦ p q _ _ _).of_functorIso
    (comparison hΦ p q v adj hv)

lemma square_boundary : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ square hΦ p q v adj hv =
    (newFrame (Φ := Φ) p q).diagram :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension_target_boundary (boundaryHomotopy (Φ := Φ) p q)) _ (oldFrame_eq hΦ p q v adj hv)

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square hΦ p q v adj hv = SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.cSource (Φ := Φ) p q (pullbackInclusion p q))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_bottom_of_boundary _ (square_boundary hΦ p q v adj hv)

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square hΦ p q v adj hv = SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (LaxQuotientPullback.dSource (Φ := Φ) p q (pullbackInclusion p q))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_left_of_boundary _ (square_boundary hΦ p q v adj hv)

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square hΦ p q v adj hv =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ q)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_top_of_boundary _ (square_boundary hΦ p q v adj hv)

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square hΦ p q v adj hv =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ p)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_right_of_boundary _ (square_boundary hΦ p q v adj hv)

end SerrePositivity.KST.LocalizingInvariants.TammePullback
