module

public import SerrePositivity.EInfinity.Hammock.ValueSupportFiniteWeak

/-!
# 元の評価の singleton 制限の弱同値

概要：実際の値の fiber が弱可縮なら、その値への元の評価の制限は弱同値。
方針：singleton の終対象性と元の fiber との同型で終射を回収する。
規約：元の評価自身の制限を使い、fiber の充填性は要求しない。
使われ方：全指定自由圏の元の評価の有限部分。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ValueSupport
open CategoryTheory Limits SerrePositivity.InfinityCategories

variable {B : Type u} {X : SSet.{u}} (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def singleton_isTerminal (β : B) :
    IsTerminal (subcomplex (𝟙 ((Functor.const SimplexCategoryᵒᵖ).obj B)) {β}).toFunctor := by
  refine IsTerminal.ofUniqueHom (fun A =>
    { app n := ↾fun _ => ⟨β, rfl⟩
      naturality _ _ _ := rfl }) ?_
  intro A f
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact (f.app n x).property

lemma singleton_restriction_weak (β : B)
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space ℓ β)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (restriction ℓ (𝟙 _) ℓ (Category.comp_id ℓ) {β}) := by
  let e := singletonFiberIso ℓ β
  let j := (singleton_isTerminal β).uniqueUpToIso terminalIsTerminal
  have hw := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence.comp hβ
  have ht : restriction ℓ (𝟙 _) ℓ (Category.comp_id ℓ) {β} ≫ j.hom =
      e.hom ≫ terminal.from _ := terminal.hom_ext _ _
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso j).isWeakHomotopyEquivalence.cancel_right
  rw [ht]
  exact hw

end SerrePositivity.EInfinity.Hammock.ValueSupport
