module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.IdentityLaxVerdier

public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxKernel
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceAdjunction

/-!
概要：恒等矢印の対角・恒等 lax 圏・cofiber 差は実 Verdier 列をなす。
方針：元の対角の充満忠実性と真の核を、差の実右随伴からの局所化に接続する。
規約：Q の安定性だけを入力する。使われ方：一般商の列を比較する普遍の列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax
variable (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

lemma difference_isVerdier :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (exactDiagonal Q) (exactLaxDifference (𝟙 Q) (𝟙 Q)) where
  fullyFaithful := diagonal_fullyFaithful Q
  kernel := difference_kernel Q
  quotient := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.invertedEdges_eq_cofiber_kernel (exactDiagonal Q)
      (exactLaxDifference (𝟙 Q) (𝟙 Q)) (difference_kernel Q)]
    exact laxDifference_isLocalization (𝟙 Q) (𝟙 Q) (𝟙 Q.obj) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.identityAdjunction Q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl Q.obj).isFullyFaithful

def verdierSequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u} where
  left := Q
  middle := laxCategory (𝟙 Q) (𝟙 Q)
  right := Q
  inclusion := exactDiagonal Q
  projection := exactLaxDifference (𝟙 Q) (𝟙 Q)
  isVerdier := difference_isVerdier Q

end SerrePositivity.KST.LocalizingInvariants.IdentityLax
