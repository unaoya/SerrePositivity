module
public import SerrePositivity.KST.Fibration.WeakCofiberCompletion
public import SerrePositivity.KST.Fibration.WeakStringCofibers

/-! # 元の W 辺の同じ cofiber 選択による完全な切断と同値 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {T : StableModel.{u}}
  (e : T ⟶ weakArrowModel q)

/-- 元の指定辺と既存の cofiber 選択を使う厳密な切断。 -/
def weakCofiberCompletionSectionMap : T.carrier ⟶ (weakCofiberCompletionModel q e).carrier :=
  pullback.lift ((e ≫ (weakArrowCofiberEquivalence q).inv).val) (𝟙 _) (by
    change ((e ≫ (weakArrowCofiberEquivalence q).inv) ≫
      (weakArrowCofiberEquivalence q).hom).val = _
    rw [Category.assoc, weakArrowCofiberEquivalence_inv_hom, Category.comp_id]
    rfl)

lemma weakCofiberCompletionSectionMap_forget :
    weakCofiberCompletionSectionMap q e ≫ (weakCofiberCompletionForget q e).val = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- 切断の完全性は、元の忘却射影の普遍性の反映から従う。 -/
def weakCofiberCompletionSection : T ⟶ weakCofiberCompletionModel q e :=
  ⟨weakCofiberCompletionSectionMap q e, by
    apply preservesCofiberData_of_trivialProjection (weakCofiberCompletionForget q e).val
    rw [weakCofiberCompletionSectionMap_forget]
    exact preservesCofiberData_id _⟩

lemma weakCofiberCompletionSection_forget :
    weakCofiberCompletionSection q e ≫ weakCofiberCompletionForget q e = 𝟙 T :=
  Subtype.ext (weakCofiberCompletionSectionMap_forget q e)

/-- 切断の元の cofiber は、指定した辺の既存の同じ補完。 -/
lemma weakCofiberCompletionSection_cofiber :
    weakCofiberCompletionSection q e ≫ weakCofiberCompletionCofiber q e =
      e ≫ (weakArrowCofiberEquivalence q).inv := Subtype.ext (pullback.lift_fst _ _ _)

/-- 元の忘却射影と同じ切断は、完全な順逆と coherent な二つの逆同型を持つ。 -/
def weakCofiberCompletionEquivalence :
    StableModelEquivalence (weakCofiberCompletionModel q e) T where
  hom := weakCofiberCompletionForget q e
  inv := weakCofiberCompletionSection q e
  homInvIso := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (weakCofiberCompletionForget q e).val _ _ (by
    change ((weakCofiberCompletionForget q e ≫ weakCofiberCompletionSection q e) ≫
      weakCofiberCompletionForget q e).val = _
    rw [Category.assoc, weakCofiberCompletionSection_forget, Category.comp_id]
    rfl)
  invHomIso := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakCofiberCompletionSection q e ≫ weakCofiberCompletionForget q e).val
      (𝟙 T.carrier)
    rw [weakCofiberCompletionSection_forget]
    exact Iso.refl _

end SerrePositivity.KST.Fibration
