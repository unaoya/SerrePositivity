module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameEdgesHomotopy
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
variable (Φ : StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def oldFrame : SquareFrame Sp.{u} := squareFrameOfEdges
  (coherentNerveEdge (valueMap Φ (LaxQuotientRelativeSquare.cSource p q i)))
  (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r)))
  (coherentNerveEdge (valueMap Φ (LaxQuotientRelativeSquare.dSource p q i)))
  (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r)))

def newFrame : SquareFrame Sp.{u} := squareFrameOfEdges
  (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q)))
  (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r)))
  (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxSnd p q)))
  (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r)))

lemma oldFrame_eq : oldFrame Φ p q i r =
    SquareFrame.ofSquare (LaxQuotientRelativeSquare.valueSquare p q i r h Φ) := by
  apply SquareFrame.ext
  · exact (LaxQuotientRelativeSquare.valueSquare_bottom p q i r h Φ).symm
  · exact (LaxQuotientRelativeSquare.valueSquare_top p q i r h Φ).symm
  · exact (LaxQuotientRelativeSquare.valueSquare_left p q i r h Φ).symm
  · exact (LaxQuotientRelativeSquare.valueSquare_right p q i r h Φ).symm

lemma valueMap_comp_hom {U V W : StableCategory.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    SpectrumHo.hom (valueMap Φ (F ≫ G)) = SpectrumHo.hom (valueMap Φ F ≫ valueMap Φ G) := by
  rw [SpectrumHo.hom_comp]
  exact (stableValueFunctor Φ).map_comp F G

def boundaryHomotopy : SquareFrameHomotopy (oldFrame Φ p q i r) (newFrame Φ p q i r) :=
  squareFrameEdgesHomotopy (X := Sp.{u})
    (coherentNerveEdge (valueMap Φ (LaxQuotientRelativeSquare.cSource p q i)))
    (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q)))
    (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r)))
    (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r)))
    (coherentNerveEdge (valueMap Φ (LaxQuotientRelativeSquare.dSource p q i)))
    (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxSnd p q)))
    (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r)))
    (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r)))
    (valueMap_comp_hom Φ i (laxFst p q)) rfl (valueMap_comp_hom Φ i (laxSnd p q)) rfl

def extension : SquareFrame.PathExtension (boundaryHomotopy Φ p q i r).pathFrame
    (LaxQuotientRelativeSquare.valueSquare p q i r h Φ) :=
  (boundaryHomotopy Φ p q i r).extension _ (oldFrame_eq Φ p q i r h)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (extension Φ p q i r h).target

def comparison : FunctorIso (LaxQuotientRelativeSquare.valueSquare p q i r h Φ)
    (square Φ p q i r h) := (extension Φ p q i r h).comparison

lemma square_boundary : SquareFrame.boundaryι ≫ square Φ p q i r h =
    (newFrame Φ p q i r).diagram :=
  (boundaryHomotopy Φ p q i r).extension_target_boundary _ (oldFrame_eq Φ p q i r h)

lemma square_bottom : squareBottomEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q))).edge :=
  SquareFrame.square_bottom_of_boundary _ (square_boundary Φ p q i r h)

lemma square_left : squareLeftEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxSnd p q))).edge :=
  SquareFrame.square_left_of_boundary _ (square_boundary Φ p q i r h)

lemma square_right : squareRightEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r))).edge :=
  SquareFrame.square_right_of_boundary _ (square_boundary Φ p q i r h)

lemma square_top : squareTopEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r))).edge :=
  SquareFrame.square_top_of_boundary _ (square_boundary Φ p q i r h)

lemma square_isPullback (hQ : IsPullbackSquare
    (LaxQuotientRelativeSquare.valueSquare p q i r h Φ)) :
    IsPullbackSquare (square Φ p q i r h) :=
  IsPullbackSquare.of_functorIso hQ (comparison Φ p q i r h)

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
