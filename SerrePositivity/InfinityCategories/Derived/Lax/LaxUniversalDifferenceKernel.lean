module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

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
  have hz := inclusion_difference_zero p q i r h x
  have hi := (laxDifference_zero_iff (𝟙 Q) (𝟙 Q) _).mp hz
  change IsEquivalencePathVertex (((i.hom ≫ lift p q r) ≫
    F2.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj)).app (Opposite.op ⦋0⦌) x) at hi
  rw [Category.assoc, lift_arrow] at hi
  exact hi

def inclusionArrowComparison : FunctorIso (i.hom ≫ connectingArrow p q r)
    ((i.hom ≫ first p q r) ≫ constantFunctorMap (Δ[1] : SSet.{u}) Q.obj) := by
  have e := EquivalenceArrowFamily.comparison (i.hom ≫ connectingArrow p q r)
    (inclusion_connectingArrow_invertible p q i r h)
  simpa only [first, Category.assoc, lift_fst] using e

def inclusionDiagonalIso : FunctorIso (i.hom ≫ lift p q r)
    ((i.hom ≫ first p q r) ≫ IdentityLax.diagonal Q) := by
  have e := FunctorIso.postcomp (inclusionArrowComparison p q i r h) (arrowLaxInverse Q.obj)
  simpa only [lift, IdentityLax.diagonal, Category.assoc] using e

def inclusionCLegDiagonalIso : FunctorIso (i.hom ≫ lift p q r)
    (((i.hom ≫ (laxFst p q).hom) ≫ (laxQuotientCLeg p q r).hom) ≫
      IdentityLax.diagonal Q) := by
  have e := FunctorIso.postcomp (FunctorIso.precomp (firstCLegIso p q r) i.hom)
    (IdentityLax.diagonal Q)
  have ec : FunctorIso ((i.hom ≫ first p q r) ≫ IdentityLax.diagonal Q)
      (((i.hom ≫ (laxFst p q).hom) ≫ (laxQuotientCLeg p q r).hom) ≫
        IdentityLax.diagonal Q) := by
    simpa only [Category.assoc] using e
  exact inclusionDiagonalIso p q i r h ≪≫ ec

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
