module

public import SerrePositivity.KST.LocalizingInvariants.CofiberExactNaturality
public import SerrePositivity.KST.LocalizingInvariants.TammeArrowDenominators
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexMarkedCover

/-!
概要：元の cofiber 関手は矢印圏上の点ごとの分母を、元の商で可逆となる辺へ写す。
方針：完全な差との全関手の自然比較で分母保存を移し、商の反転集合の厳密な同定を使う。
規約：商の安定性は不使用。使われ方：cofiber 関手の矢印局所化への実降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma tammeCofiber_difference_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (laxCategory p q).obj (𝟙 _) ≫ laxDifference p q)
    (tammeArrowLocalizingEdges p q) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges
      ((ihom (Δ[1] : SSet.{u})).map (laxDifference p q) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber E.obj (𝟙 _)) (tammeArrowLocalizingEdges p q) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges.comp (H := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber E.obj (𝟙 _))
    rw [tammeArrowLocalizingEdges_eq_invertedDifference]
    exact Set.Subset.refl _
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges at h ⊢
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.invertedEdges_functorIso (CofiberFamily.exactNaturality (laxDifference p q))]
  exact h

lemma tammeCofiber_quotient_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (laxCategory p q).obj (𝟙 _) ≫ tammeQuotientMap p q)
    (tammeArrowLocalizingEdges p q) := by
  intro s hs
  have hd : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (laxCategory p q).obj (𝟙 _)).app (Opposite.op ⦋1⦌) s ∈
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (laxDifference p q) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertedEdges_comp_iff _ _ s).mp (tammeCofiber_difference_inverts p q hs)
  rw [← tammeLocalizingEdges_eq, ← tammeQuotientMap_invertedEdges] at hd
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertedEdges_comp_iff _ _ s).mpr hd

end SerrePositivity.KST.LocalizingInvariants
