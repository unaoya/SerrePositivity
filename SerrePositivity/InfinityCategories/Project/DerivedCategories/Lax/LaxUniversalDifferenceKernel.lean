module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.EquivalenceArrowFamily
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceCLeg

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

include h in
lemma inclusion_difference_zero (x : A.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((i.hom ≫ lift p q r) ≫ laxDifference (𝟙 Q) (𝟙 Q)).app
      (Opposite.op ⦋0⦌) x) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (differenceIso p q r) i.hom
  have hz := (h.kills_inclusion x).of_vertexIso (e.app x).symm
  simpa only [Category.assoc] using hz

include h in
lemma inclusion_connectingArrow_invertible (x : A.obj _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    ((i.hom ≫ connectingArrow p q r).app (Opposite.op ⦋0⦌) x) := by
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.inclusion_difference_zero p q i r h x
  have hi := (laxDifference_zero_iff (𝟙 Q) (𝟙 Q) _).mp hz
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (((i.hom ≫ lift p q r) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj)).app (Opposite.op ⦋0⦌) x) at hi
  rw [Category.assoc, lift_arrow] at hi
  exact hi

def inclusionArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i.hom ≫ connectingArrow p q r)
    ((i.hom ≫ first p q r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) Q.obj) := by
  have e := EquivalenceArrowFamily.comparison (i.hom ≫ connectingArrow p q r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.inclusion_connectingArrow_invertible p q i r h)
  simpa only [first, Category.assoc, lift_fst] using e

def inclusionDiagonalIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i.hom ≫ lift p q r)
    ((i.hom ≫ first p q r) ≫ IdentityLax.diagonal Q) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.inclusionArrowComparison p q i r h) (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Q.obj)
  simpa only [lift, IdentityLax.diagonal, Category.assoc] using e

def inclusionCLegDiagonalIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i.hom ≫ lift p q r)
    (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom) ≫
      IdentityLax.diagonal Q) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.firstCLegIso p q r) i.hom)
    (IdentityLax.diagonal Q)
  have ec : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((i.hom ≫ first p q r) ≫ IdentityLax.diagonal Q)
      (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom) ≫
        IdentityLax.diagonal Q) := by
    simpa only [Category.assoc] using e
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.inclusionDiagonalIso p q i r h ≪≫ ec

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
