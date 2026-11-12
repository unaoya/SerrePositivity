module
public import SerrePositivity.KST.Fibration.WeakArrowCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
public import SerrePositivity.KST.SConstruction.MultiRealizationEquivalence

/-! # W 辺図式と相対 cofiber 図式の完全な同値

底辺を取る元の射影の全境界持ち上げから、coherent な逆を構成する。
W 辺図式の安定性・完全性を導き、K-1/K-2 の全正有限反復実現へ比較を渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- W 辺図式の安定性は、元の全相対 cofiber 補完の射影から従う。 -/
instance weakArrowCategory_isStable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (weakArrowCategory q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_target_of_trivialKanFibration (weakCofiberProjection q)

/-- W 辺図式を K-1 の安定な入力として保持する。 -/
def weakArrowModel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : StableModel.{u} where
  carrier := weakArrowCategory q
  quasicategory := inferInstance
  stable := inferInstance

/-- 元の cofiber 射影を順方向に持つ、完全な順逆と coherent な二つの逆同型。 -/
def weakArrowCofiberEquivalence {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    StableModelEquivalence (weakCofiberModel q) (weakArrowModel q) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (weakCofiberProjection q)
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact {
    hom := ⟨e.hom, hh.preservesZero, hh.preservesCofiber⟩
    inv := ⟨e.inv, hi.preservesZero, hi.preservesCofiber⟩
    homInvIso := e.homInvIso
    invHomIso := e.invHomIso }

/-- 同値の順射は、元の底辺を取る相対 cofiber 射影そのもの。 -/
lemma weakArrowCofiberEquivalence_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakArrowCofiberEquivalence q).hom.val = weakCofiberProjection q := rfl

/-- 元の W 底辺への比較は、全正有限反復 S• 実現で局所化同型となる。 -/
lemma weakArrowCofiber_multiRealization_localized_isIso
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).hom)) :=
  multiRealization_map_localized_isIso_of_equivalence r (weakArrowCofiberEquivalence q)

end SerrePositivity.KST.Fibration
