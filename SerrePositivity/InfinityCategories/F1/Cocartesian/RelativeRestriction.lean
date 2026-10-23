module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.Isofibration
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorRestrictionFiber
public import SerrePositivity.InfinityCategories.Core.PrecompositionPushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：cocartesian 標的への相対 Hom は単射な前合成同値による制限で全境界を持ち上げる。
方針：cocartesian fibration の同値持ち上げを、pushout-product と閉構造の随伴で移す。
規約：標的が left fibration であるとは仮定せず、底の quasicategory 性だけを追加する。
使われ方：universal scaffold に沿う全相対 Hom の制限同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 単射な前合成同値に沿う相対内部 Hom の制限は、cocartesian 標的でも自明 Kan。 -/
lemma trivialKanFibration_relativeHom_of_cocartesian_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (i : D ⟶ A) [Mono i] (hi : IsPrecompositionEquivalence i)
    (sq' : internalHom.PullbackObjObj i p) : TrivialKanFibration sq'.π := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    i (boundary n).ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact cocartesianFibration_kanEquivalenceLifting p sq.ι
    (mono_pushoutObjObj_ι i (boundary n).ι sq) (hi.pushoutObjObj (boundary n).ι sq)

/-- 固定した底の図式上でも、cocartesian 標的の相対関手の単射な同値による制限は自明 Kan。 -/
lemma relativeFunctorPre_trivialKanFibration_of_cocartesian
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (a : A ⟶ B) (i : D ⟶ A) [Mono i] (hi : IsPrecompositionEquivalence i) :
    TrivialKanFibration (relativeFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := trivialKanFibration_relativeHom_of_cocartesian_of_precompositionEquivalence p i hi sq'
  exact relativeFunctorPre_trivialKanFibration_of_relativeHom p a i sq'

end SerrePositivity.InfinityCategories
