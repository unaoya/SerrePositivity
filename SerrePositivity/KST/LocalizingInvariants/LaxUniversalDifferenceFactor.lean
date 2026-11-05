module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceFirst
public import SerrePositivity.KST.LocalizingInvariants.AdjointLocalizationFactor
public import SerrePositivity.KST.LocalizingInvariants.LaxSemiorthogonal

/-!
概要：普遍差への比較の第一射影は、元の C 射影を通して分解する。
方針：D 上の零化を核全体へ延ばし、反射単位の像の可逆性を使う。
規約：第一射影と C 包含を元の全関手のまま保持。使われ方：一般商の C 脚との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (r : ExactMap (laxCategory p q) Q)

lemma first_inverts : InvertsEdges (first p q r) (invertedEdges (laxFst p q).hom) := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.invertedEdges_eq_cofiber_kernel (LaxInclusion.exactFromD p q) (laxFst p q)
    (laxSemiorthogonal p q).kernel]
  exact (inverts_iff_kills_inclusion (LaxInclusion.exactFromD p q)
    (⟨first p q r, inferInstance⟩ : ExactMap (laxCategory p q) Q)).mpr
      (fromD_first_zero p q r)

def firstFactorIso : FunctorIso (first p q r)
    (((laxFst p q).hom ≫ LaxInclusion.fromC p q) ≫ first p q r) :=
  AdjointLocalization.factorIso (LaxInclusion.fromCAdjunction p q)
    (first p q r) (first_inverts p q r)

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
