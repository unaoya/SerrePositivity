module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProductFiberVertices
public import SerrePositivity.KST.LocalizingInvariants.RestrictedFunctorEdgeEvaluation

/-!
概要：実 product fiber の全図式比較は中項と右項で指定された同型を保持する。
方針：右辺への制限の同じ一単体を評価し、区間同型の両端の計算を適用する。
規約：元の比較辺を使う。使われ方：元の両射影との整合と実 pullback 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productComponentsSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance productComponentsSquareQuasicategory :
    Quasicategory (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) := F2.quasicategory_tensor _ _
local instance productComponentsNerveQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

lemma laxQuotientProductFiberComparison_middle_arrow :
    Arrow.mk (FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).hom =
      Arrow.mk (hΦ.laxQuotientProjectionMiddleIso p q i r h).inv := by
  have he := restrictedFunctorEdge_evaluation_arrow squareRightEdge
    (hΦ.laxQuotientProductFiberEdge p q i r h)
    (hΦ.laxQuotientProductArrowIso p q i r h).edge
    (hΦ.laxQuotientProductFiberEdge_right p q i r h)
    (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)))
  rw [FunctorIso.edge_homMk] at he
  have hv : squareRightEdge.{u + 1}.app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))) =
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl
  rw [hv] at he
  exact (functorIso_toNatIso_hom_app_arrow
    (hΦ.laxQuotientProductFiberComparison p q i r h) _).trans
      (he.trans (hΦ.laxQuotientProductArrowIso_source p q i r h))

lemma laxQuotientProductFiberComparison_right_arrow :
    Arrow.mk (FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))).hom =
      Arrow.mk (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).inv := by
  have he := restrictedFunctorEdge_evaluation_arrow squareRightEdge
    (hΦ.laxQuotientProductFiberEdge p q i r h)
    (hΦ.laxQuotientProductArrowIso p q i r h).edge
    (hΦ.laxQuotientProductFiberEdge_right p q i r h)
    (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)))
  rw [FunctorIso.edge_homMk] at he
  have hv : squareRightEdge.{u + 1}.app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))) =
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl
  rw [hv] at he
  exact (functorIso_toNatIso_hom_app_arrow
    (hΦ.laxQuotientProductFiberComparison p q i r h) _).trans
      (he.trans (hΦ.laxQuotientProductArrowIso_target p q i r h))

lemma laxQuotientProductFiberComparison_middle :
    FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      hΦ.laxQuotientProductFiberMiddleIso p q i r h ≪≫
        (hΦ.laxQuotientProjectionMiddleIso p q i r h).symm := by
  apply Iso.ext
  exact hom_eq_transport_of_arrow_eq _ _
    (congrArg SSet.HomotopyCategory.mk (hΦ.laxQuotientProductFiber_middle_vertex p q i r h))
    (hΦ.laxQuotientProductFiberComparison_middle_arrow p q i r h)

lemma laxQuotientProductFiberComparison_right :
    FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      hΦ.laxQuotientProductFiberRightIso p q i r h ≪≫
        (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).symm := by
  apply Iso.ext
  exact hom_eq_transport_of_arrow_eq _ _
    (congrArg SSet.HomotopyCategory.mk (hΦ.laxQuotientProductFiber_right_vertex p q i r h))
    (hΦ.laxQuotientProductFiberComparison_right_arrow p q i r h)

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
