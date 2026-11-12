module
public import SerrePositivity.KST.Fibration.ComposableWeakArrowEndpointPullback
public import SerrePositivity.KST.Fibration.FamilyExactness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-! # 第二 W 辺の全 cofiber 補完を持つ安定な二辺図式圏 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 接続した二辺の第二辺と、その全相対 cofiber 補完を保持する厳密引き戻し。 -/
def completedTwoCategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : SSet.{u} :=
  pullback (weakCofiberProjection q) (composableWeakNextMap q)

/-- 補完を忘れる元の射影は全境界持ち上げを持つ。 -/
instance completedTwoProjection_trivialKanFibration {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd (weakCofiberProjection q) (composableWeakNextMap q)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

instance completedTwoCategory_quasicategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    Quasicategory (completedTwoCategory q) :=
  quasicategory_of_innerFibration
    (pullback.snd (weakCofiberProjection q) (composableWeakNextMap q))

instance completedTwoCategory_isStable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (completedTwoCategory q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_trivialKanFibration
    (pullback.snd (weakCofiberProjection q) (composableWeakNextMap q))

/-- 第二辺の補完を持つ図式圏を元の安定模型として保持する。 -/
def completedTwoModel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : StableModel.{u} where
  carrier := completedTwoCategory q
  quasicategory := inferInstance
  stable := inferInstance

/-- 元の接続した二辺へ補完を忘れる完全関手。 -/
def completedTwoForget {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoModel q ⟶ composableWeakArrowModel q :=
  ⟨pullback.snd _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber⟩

instance completedTwoForget_trivialKanFibration {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (completedTwoForget q).val :=
  inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
    (pullback.snd (weakCofiberProjection q) (composableWeakNextMap q)))

/-- 保持している第二辺の全相対 cofiber 図式を抽出する完全関手。 -/
def completedTwoCofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoModel q ⟶ weakCofiberModel q :=
  ⟨pullback.fst _ _, by
    apply preservesCofiberData_of_trivialProjection (weakCofiberProjection q)
    rw [pullback.condition]
    exact (completedTwoForget q).property.comp (composableWeakNextExact q).property⟩

/-- 元の二辺の第二辺は、同じ相対 cofiber 補完の底辺そのもの。 -/
lemma completedTwoCofiber_projection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoCofiber q ≫ (weakArrowCofiberEquivalence q).hom =
      completedTwoForget q ≫ composableWeakNextExact q :=
  Subtype.ext pullback.condition

end SerrePositivity.KST.Fibration
