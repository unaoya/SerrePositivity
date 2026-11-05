module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullbackComparison
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierReflectiveCompatibility
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientShiftReflective

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
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (adj : QCatAdjunction q.hom v) (hv : IsFullyFaithful v)

def original : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  LaxQuotientPullback.square hΦ p q (pullbackInclusion p q) (exactLaxDifference p q)
    (laxDifference_isVerdier p q v adj hv)

def oldFrame : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges
  (coherentNerveEdge (LaxQuotientPullback.cSource (Φ := Φ) p q (pullbackInclusion p q)))
  (coherentNerveEdge (LaxQuotientPullback.dLeg (Φ := Φ) p q (exactLaxDifference p q)))
  (coherentNerveEdge (LaxQuotientPullback.dSource (Φ := Φ) p q (pullbackInclusion p q)))
  (coherentNerveEdge (LaxQuotientPullback.cLeg (Φ := Φ) p q (exactLaxDifference p q)))

lemma oldFrame_eq : oldFrame (Φ := Φ) p q = _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare (original hΦ p q v adj hv) := by
  apply _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.ext
  · exact (LaxQuotientPullback.square_bottom hΦ p q _ _ _).symm
  · exact (LaxQuotientPullback.square_top hΦ p q _ _ _).symm
  · exact (LaxQuotientPullback.square_left hΦ p q _ _ _).symm
  · exact (LaxQuotientPullback.square_right hΦ p q _ _ _).symm

def newFrame : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges
  (coherentNerveEdge (LaxQuotientPullback.cSource (Φ := Φ) p q (pullbackInclusion p q)))
  (coherentNerveEdge (valueMap Φ q))
  (coherentNerveEdge (LaxQuotientPullback.dSource (Φ := Φ) p q (pullbackInclusion p q)))
  (coherentNerveEdge (valueMap Φ p))

def boundaryHomotopy : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy (oldFrame (Φ := Φ) p q) (newFrame (Φ := Φ) p q) :=
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.squareFrameEdgesHomotopy _ _ _ _ _ _ _ _ rfl
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_laxQuotientDLeg_cofiber p q Φ) rfl (_root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_laxQuotientCLeg_cofiber p q Φ)

def extension : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension (boundaryHomotopy (Φ := Φ) p q).pathFrame
    (original hΦ p q v adj hv) :=
  (boundaryHomotopy (Φ := Φ) p q).extension _ (oldFrame_eq hΦ p q v adj hv)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (extension hΦ p q v adj hv).target

def comparison : FunctorIso (original hΦ p q v adj hv) (square hΦ p q v adj hv) :=
  (extension hΦ p q v adj hv).comparison

lemma square_isPullback : IsPullbackSquare (square hΦ p q v adj hv) :=
  (LaxQuotientPullback.square_isPullback hΦ p q _ _ _).of_functorIso
    (comparison hΦ p q v adj hv)

lemma square_boundary : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ square hΦ p q v adj hv =
    (newFrame (Φ := Φ) p q).diagram :=
  (boundaryHomotopy (Φ := Φ) p q).extension_target_boundary _ (oldFrame_eq hΦ p q v adj hv)

lemma square_bottom : squareBottomEdge ≫ square hΦ p q v adj hv = SSet.yonedaEquiv.symm
    (coherentNerveEdge (LaxQuotientPullback.cSource (Φ := Φ) p q (pullbackInclusion p q))).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_bottom_of_boundary _ (square_boundary hΦ p q v adj hv)

lemma square_left : squareLeftEdge ≫ square hΦ p q v adj hv = SSet.yonedaEquiv.symm
    (coherentNerveEdge (LaxQuotientPullback.dSource (Φ := Φ) p q (pullbackInclusion p q))).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_left_of_boundary _ (square_boundary hΦ p q v adj hv)

lemma square_top : squareTopEdge ≫ square hΦ p q v adj hv =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ q)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_top_of_boundary _ (square_boundary hΦ p q v adj hv)

lemma square_right : squareRightEdge ≫ square hΦ p q v adj hv =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ p)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_right_of_boundary _ (square_boundary hΦ p q v adj hv)

end SerrePositivity.KST.LocalizingInvariants.TammePullback
