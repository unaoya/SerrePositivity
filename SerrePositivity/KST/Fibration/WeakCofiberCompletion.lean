module
public import SerrePositivity.KST.Fibration.WeakArrowEquivalence
public import SerrePositivity.KST.Fibration.FamilyExactness
public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement

/-! # W 辺を持つ任意の安定図式の全相対 cofiber 補完 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
variable {B C : StableCategory.{u}} (q : ExactMap B C) {T : StableModel.{u}}
  (e : T ⟶ weakArrowModel q)

/-- 指定された元の実 W 辺の、全相対 cofiber 補完を保持する引き戻し。 -/
def weakCofiberCompletionCategory : SSet.{u} := pullback (weakCofiberProjection q) e.val

instance weakCofiberCompletionProjection_trivialKanFibration :
    TrivialKanFibration (pullback.snd (weakCofiberProjection q) e.val) :=
  trivialKanFibration_pullback_snd _ _

instance weakCofiberCompletionCategory_quasicategory :
    Quasicategory (weakCofiberCompletionCategory q e) :=
  quasicategory_of_innerFibration (pullback.snd (weakCofiberProjection q) e.val)

instance weakCofiberCompletionCategory_isStable :
    IsStable (weakCofiberCompletionCategory q e) :=
  InfinityCategories.isStable_of_trivialKanFibration (pullback.snd (weakCofiberProjection q) e.val)

/-- 元の全相対 cofiber 補完を持つ安定模型。 -/
def weakCofiberCompletionModel : StableModel.{u} where
  carrier := weakCofiberCompletionCategory q e
  quasicategory := inferInstance
  stable := inferInstance

/-- 補完だけを忘れる元の射影は完全。 -/
def weakCofiberCompletionForget : weakCofiberCompletionModel q e ⟶ T :=
  ⟨pullback.snd _ _, IsExactFunctor.preservesZero, IsExactFunctor.preservesCofiber⟩

instance weakCofiberCompletionForget_trivialKanFibration :
    TrivialKanFibration (weakCofiberCompletionForget q e).val :=
  inferInstanceAs (TrivialKanFibration (pullback.snd (weakCofiberProjection q) e.val))

/-- 保持した元の相対 cofiber 図式を抽出する完全関手。 -/
def weakCofiberCompletionCofiber : weakCofiberCompletionModel q e ⟶ weakCofiberModel q :=
  ⟨pullback.fst _ _, by
    apply preservesCofiberData_of_trivialProjection (weakCofiberProjection q)
    rw [pullback.condition]
    exact (weakCofiberCompletionForget q e).property.comp e.property⟩

/-- 補完から元の実 W 辺を取ると、忘却後の同じ指定辺を回収する。 -/
lemma weakCofiberCompletionCofiber_projection :
    weakCofiberCompletionCofiber q e ≫ (weakArrowCofiberEquivalence q).hom =
      weakCofiberCompletionForget q e ≫ e := Subtype.ext pullback.condition

end SerrePositivity.KST.Fibration
