module
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquareFrameFunctoriality

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameEdgesHomotopy
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor

/-!
概要：指定比較道を持つ値の正方形を、元の BF 合成二脚を持つ正方形へ移す。
方針：各辺を端点恒等のホモトピーで変形し、境界 path を本体へ延長する。
規約：元の正方形との全関手同型を保持。使われ方：実 product fiber との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def oldFrame : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.cSource p q i)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.dSource p q i)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)))

def newFrame : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxSnd p q)))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)))

lemma oldFrame_eq : oldFrame Φ p q i r =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ext
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare_bottom p q i r h Φ).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare_top p q i r h Φ).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare_left p q i r h Φ).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare_right p q i r h Φ).symm

lemma valueMap_comp_hom {U V W : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    SpectrumHo.hom (valueMap Φ (F ≫ G)) = SpectrumHo.hom (valueMap Φ F ≫ valueMap Φ G) := by
  rw [SpectrumHo.hom_comp]
  exact (stableValueFunctor Φ).map_comp F G

def boundaryHomotopy : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (oldFrame Φ p q i r) (newFrame Φ p q i r) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy (X := Sp.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.cSource p q i)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.dSource p q i)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxSnd p q)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)))
    (valueMap_comp_hom Φ i (laxFst p q)) rfl (valueMap_comp_hom Φ i (laxSnd p q)) rfl

def extension : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.pathFrame (boundaryHomotopy Φ p q i r))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension (boundaryHomotopy Φ p q i r)) _ (oldFrame_eq Φ p q i r h)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (extension Φ p q i r h).target

def comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ)
    (square Φ p q i r h) := (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.comparison (extension Φ p q i r h))

lemma square_boundary : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ square Φ p q i r h =
    (newFrame Φ p q i r).diagram :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension_target_boundary (boundaryHomotopy Φ p q i r)) _ (oldFrame_eq Φ p q i r h)

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_bottom_of_boundary _ (square_boundary Φ p q i r h)

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxSnd p q))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_left_of_boundary _ (square_boundary Φ p q i r h)

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_right_of_boundary _ (square_boundary Φ p q i r h)

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.square_top_of_boundary _ (square_boundary Φ p q i r h)

lemma square_isPullback (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (square Φ p q i r h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPullbackSquare.of_functorIso hQ (comparison Φ p q i r h)

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
