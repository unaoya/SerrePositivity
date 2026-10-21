module

public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiber
public import SerrePositivity.InfinityCategories.F2.QCatTensorAndArrowObjects

/-!
概要：実 product fiber 四角形の中項と右項は指定 BF 対象で、左項は元の E(A) と同値。
方針：固定された右辺の両端を回収し、全四角形の同型の左下成分を評価する。
規約：三頂点は同じ実四角形に属する。使われ方：d8 の元の値への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productVerticesSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance productVerticesSquareQuasicategory :
    Quasicategory (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) := F2.quasicategory_tensor _ _
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

lemma laxQuotientProductFiber_middle_vertex :
    squareVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 0 =
      coherentNerveVertex (Binary.obj (value Φ C) (value Φ D)) :=
  fiberSquare_source_vertex (hΦ.laxQuotientProductFiberSquare p q i r h)

lemma laxQuotientProductFiber_right_vertex :
    squareVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 1 =
      coherentNerveVertex (value Φ Q) :=
  fiberSquare_target_vertex (hΦ.laxQuotientProductFiberSquare p q i r h)

def laxQuotientProductFiberLeftIso :
    squareHoVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 0 0 ≅
      SpectrumHo.obj (value Φ A) :=
  FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≪≫
      hΦ.fiberLeftIso (laxQuotientVerdierSequence p q i r h)

def laxQuotientProductFiberMiddleIso :
    squareHoVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 0 ≅
      SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (hΦ.laxQuotientProductFiber_middle_vertex p q i r h))

def laxQuotientProductFiberRightIso :
    squareHoVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 1 ≅
      SpectrumHo.obj (value Φ Q) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (hΦ.laxQuotientProductFiber_right_vertex p q i r h))

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
