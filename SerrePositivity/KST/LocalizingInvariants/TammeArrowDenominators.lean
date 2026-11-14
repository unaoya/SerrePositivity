module

public import SerrePositivity.KST.LocalizingInvariants.PointwiseLocalizingEdges
public import SerrePositivity.KST.LocalizingInvariants.ExactArrowMap
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactKernelDenominators
public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientDetection

/-!
概要：矢印圏上の点ごとの Tamme 分母を、元の安定な核の cofiber 分母と同定する。
方針：矢印の零性を両端で判定し、完全な差の矢印関手と商への矢印射影の反転辺を比較。
規約：商の矢印圏の安定性は仮定しない。使われ方：coherent な分母の共通細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def tammeArrowKernel : Set ((_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.stableArrowCategory (laxCategory p q)).obj _⦋0⦌) :=
  {v | ∀ i : Fin 2, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (laxCategory p q).obj)
    (stdSimplex.obj₀Equiv.symm i)).app (Opposite.op ⦋0⦌) v ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)}

lemma tammeArrowKernel_eq_exactKernel :
    tammeArrowKernel p q = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel (exactArrowMap (exactLaxDifference p q)) := by
  ext v
  change (∀ i : Fin 2, _ ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)) ↔
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((ihom (Δ[1] : SSet.{u})).map (laxDifference p q)).app (Opposite.op ⦋0⦌) v)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowVertex_isZero_iff]
  apply forall_congr'
  intro i
  have h := congrArg (fun a => a.app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation (laxDifference p q) i)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := E.obj) (stdSimplex.obj₀Equiv.symm i)).app
      (Opposite.op ⦋0⦌) (((ihom (Δ[1] : SSet.{u})).map (laxDifference p q)).app
        (Opposite.op ⦋0⦌) v) = _ at h
  rw [h]
  exact (exactLaxDifference_kernel p q _).symm

lemma tammeArrowKernel_stableClosure :
    {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (tammeArrowKernel p q) v} = tammeArrowKernel p q := by
  rw [tammeArrowKernel_eq_exactKernel]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel_stableClosure _

def tammeArrowLocalizingEdges : Set ((_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.stableArrowCategory (laxCategory p q)).obj _⦋1⦌) :=
  pointwiseLocalizingEdges (Δ[1] : SSet.{u}) (laxCategory p q).obj (tammeLocalizingEdges p q)

lemma tammeArrowLocalizingEdges_eq_invertedDifference :
    tammeArrowLocalizingEdges p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges ((ihom (Δ[1] : SSet.{u})).map (laxDifference p q)) := by
  rw [invertedEdges_ihom_map]
  exact congrArg (pointwiseLocalizingEdges (Δ[1] : SSet.{u}) (laxCategory p q).obj)
    (tammeLocalizingEdges_eq p q)

lemma tammeArrowLocalizingEdges_eq_invertedQuotient :
    tammeArrowLocalizingEdges p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges ((ihom (Δ[1] : SSet.{u})).map (tammeQuotientMap p q)) := by
  rw [invertedEdges_ihom_map, tammeQuotientMap_invertedEdges]
  rfl

lemma tammeArrowLocalizingEdges_eq_cofiber :
    tammeArrowLocalizingEdges p q = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (tammeArrowKernel p q) := by
  rw [tammeArrowLocalizingEdges_eq_invertedDifference, tammeArrowKernel_eq_exactKernel]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.invertedEdges_eq_cofiber_exactKernel (exactArrowMap (exactLaxDifference p q))

lemma tammeArrowLocalizingEdges_stableClosure :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (tammeArrowKernel p q) v} =
      tammeArrowLocalizingEdges p q := by
  rw [tammeArrowKernel_stableClosure, tammeArrowLocalizingEdges_eq_cofiber]

end SerrePositivity.KST.LocalizingInvariants
