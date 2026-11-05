module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiber
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatTensorAndArrowObjects

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
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

end SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberLeftIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberLeftIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberLeftIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberRightIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberRightIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberRightIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiber_middle_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_middle_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiber_right_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_right_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productVerticesSimplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.productVerticesSimplicialCategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productVerticesSimplicialCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.productVerticesSquareQuasicategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productVerticesSquareQuasicategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberLeftIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberLeftIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberRightIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberRightIso._proof_1
