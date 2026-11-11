module
public import SerrePositivity.KST.Fibration.ComposableWeakArrows
public import SerrePositivity.KST.Fibration.WeakStringEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence

/-! # 二辺の W 列と接続した二辺の図式圏の比較同値

元の内ホーンへの制限を W 条件へ制限する。
全境界持ち上げを保つので、完全な逆と全高次の比較を持つ安定圏同値が得られる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の二単体から、合成の選択を忘れた同じ内ホーンへの制限。 -/
def weakStringTwoHornRestriction {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakStringModel q ⦋2⦌).carrier ⟶ (composableWeakArrowModel q).carrier :=
  fullPredicateMap ((pre (horn 2 1).ι).app B.obj)
    (weakStringPredicate q ⦋2⦌) (composableWeakArrowPredicate q).predicate
    (fun v => (weakStringTwoPredicate_iff_horn q v).1)

/-- 制限の包含は元の内ホーンへの前合成を回収する。 -/
lemma weakStringTwoHornRestriction_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringTwoHornRestriction q ≫
      (closedStableInclusion (composableWeakArrowPredicate q)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋2⦌)).ι ≫
          (pre (horn 2 1).ι).app B.obj := rfl

/-- W 条件への制限後も、元の全境界に対する持ち上げが存在する。 -/
instance weakStringTwoHornRestriction_trivialKanFibration {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (weakStringTwoHornRestriction q) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (horn 2 1).ι).app B.obj) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)) B.obj
  exact fullPredicateMap_trivialKanFibration _ _ _ (weakStringTwoPredicate_iff_horn q)

/-- 元の二辺の制限は完全関手である。 -/
def weakStringTwoHornExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringModel q ⦋2⦌ ⟶ composableWeakArrowModel q := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (weakStringTwoHornRestriction q) := inferInstance
  exact ⟨weakStringTwoHornRestriction q, h.preservesZero, h.preservesCofiber⟩

/-- 同じ元の制限を順射に持つ、安定な図式圏の完全な同値。 -/
def weakStringTwoHornEquivalence {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    StableModelEquivalence (weakStringModel q ⦋2⦌) (composableWeakArrowModel q) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (weakStringTwoHornRestriction q)
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact {
    hom := weakStringTwoHornExact q
    inv := ⟨e.inv, hi.preservesZero, hi.preservesCofiber⟩
    homInvIso := e.homInvIso
    invHomIso := e.invHomIso }

/-- 二辺の元の圏の比較は、全正有限反復実現で局所化同型を与える。 -/
lemma weakStringTwoHorn_multiRealization_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakStringTwoHornExact q))) :=
  multiRealization_map_localized_isIso_of_equivalence r (weakStringTwoHornEquivalence q)

end SerrePositivity.KST.Fibration
