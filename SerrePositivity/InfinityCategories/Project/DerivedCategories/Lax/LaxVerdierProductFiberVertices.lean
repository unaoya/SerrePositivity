module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatTensorAndArrowObjects

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productVerticesSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance productVerticesSquareQuasicategory :
    Quasicategory (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor _ _
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

lemma laxQuotientProductFiber_middle_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (value Φ C) (value Φ D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.fiberSquare_source_vertex (hΦ.laxQuotientProductFiberSquare p q i r h)

lemma laxQuotientProductFiber_right_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ Q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.fiberSquare_target_vertex (hΦ.laxQuotientProductFiberSquare p q i r h)

def laxQuotientProductFiberLeftIso :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 0 0 ≅
      SpectrumHo.obj (value Φ A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≪≫
      hΦ.fiberLeftIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)

def laxQuotientProductFiberMiddleIso :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 0 ≅
      SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductFiber_middle_vertex hΦ) p q i r h))

def laxQuotientProductFiberRightIso :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square 1 1 ≅
      SpectrumHo.obj (value Φ Q) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductFiber_right_vertex hΦ) p q i r h))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
