module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.EquivalenceArrowFamily
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifferenceCLeg

/-!
概要：一般商の Verdier 包含上で、普遍差への比較を恒等 lax 対角へ同定する。
方針：元の差の像が零であることから矢印の可逆性を得て、始点固定で恒等族へ比較する。
規約：元の包含と C 脚を保持。使われ方：不変量の二つの実 fiber 列の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

include h in
lemma inclusion_difference_zero (x : A.obj _⦋0⦌) :
    IsZeroVertex (((i.hom ≫ lift p q r) ≫ laxDifference (𝟙 Q) (𝟙 Q)).app
      (Opposite.op ⦋0⦌) x) := by
  have e := FunctorIso.precomp (differenceIso p q r) i.hom
  have hz := (h.kills_inclusion x).of_vertexIso (e.app x).symm
  simpa only [Category.assoc] using hz

include h in
lemma inclusion_connectingArrow_invertible (x : A.obj _⦋0⦌) : IsEquivalencePathVertex
    ((i.hom ≫ connectingArrow p q r).app (Opposite.op ⦋0⦌) x) := by
  have hz := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusion_difference_zero p q i r h x
  have hi := (laxDifference_zero_iff (𝟙 Q) (𝟙 Q) _).mp hz
  change IsEquivalencePathVertex (((i.hom ≫ lift p q r) ≫
    F2.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj)).app (Opposite.op ⦋0⦌) x) at hi
  rw [Category.assoc, lift_arrow] at hi
  exact hi

def inclusionArrowComparison : FunctorIso (i.hom ≫ connectingArrow p q r)
    ((i.hom ≫ first p q r) ≫ constantFunctorMap (Δ[1] : SSet.{u}) Q.obj) := by
  have e := EquivalenceArrowFamily.comparison (i.hom ≫ connectingArrow p q r)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusion_connectingArrow_invertible p q i r h)
  simpa only [first, Category.assoc, lift_fst] using e

def inclusionDiagonalIso : FunctorIso (i.hom ≫ lift p q r)
    ((i.hom ≫ first p q r) ≫ IdentityLax.diagonal Q) := by
  have e := FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionArrowComparison p q i r h) (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse Q.obj)
  simpa only [lift, IdentityLax.diagonal, Category.assoc] using e

def inclusionCLegDiagonalIso : FunctorIso (i.hom ≫ lift p q r)
    (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom) ≫
      IdentityLax.diagonal Q) := by
  have e := FunctorIso.postcomp (FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.firstCLegIso p q r) i.hom)
    (IdentityLax.diagonal Q)
  have ec : FunctorIso ((i.hom ≫ first p q r) ≫ IdentityLax.diagonal Q)
      (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom) ≫
        IdentityLax.diagonal Q) := by
    simpa only [Category.assoc] using e
  exact _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionDiagonalIso p q i r h ≪≫ ec

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionArrowComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionArrowComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionArrowComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionCLegDiagonalIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionCLegDiagonalIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionCLegDiagonalIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionDiagonalIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionDiagonalIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionDiagonalIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusion_connectingArrow_invertible := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusion_connectingArrow_invertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusion_difference_zero := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusion_difference_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionArrowComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionArrowComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionArrowComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionArrowComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionArrowComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionArrowComparison._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionCLegDiagonalIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionCLegDiagonalIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionCLegDiagonalIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionCLegDiagonalIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionDiagonalIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionDiagonalIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionDiagonalIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionDiagonalIso._proof_2
