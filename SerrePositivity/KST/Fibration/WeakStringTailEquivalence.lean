module
public import SerrePositivity.KST.Fibration.TailWeakReflection
public import SerrePositivity.KST.Fibration.WeakArrowEquivalence

/-! # 元の全 W 列と先行列・最後の辺の貼り合わせとの完全な同値 -/

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

/-- 元の長い W 列を、同じ先行列と最後の辺の貼り合わせへ厳密に制限する。 -/
def weakStringTailRestriction {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringModel q ⦋n + 2⦌).carrier ⟶ (tailWeakModel q n).carrier :=
  fullPredicateMap ((pre (standardTailInclusion n)).app B.obj)
    (weakStringPredicate q ⦋n + 2⦌) (tailWeakPredicate q n).predicate
    (fun v => (weakStringPredicate_iff_tail q n v).1)

/-- 元の W 条件に制限しても、全境界に対する持ち上げを保持する。 -/
instance weakStringTailRestriction_trivialKanFibration {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (weakStringTailRestriction q n) := by
  have := standardTailInclusion_pre_trivialKanFibration n B.obj
  exact fullPredicateMap_trivialKanFibration _ _ _ (weakStringPredicate_iff_tail q n)

/-- 元の全高次図式を持つ制限と、完全な逆・二つの coherent な逆同型。 -/
def weakStringTailEquivalence {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    StableModelEquivalence (weakStringModel q ⦋n + 2⦌) (tailWeakModel q n) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (weakStringTailRestriction q n)
  have hh := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact {
    hom := ⟨e.hom, hh.preservesZero, hh.preservesCofiber⟩
    inv := ⟨e.inv, hi.preservesZero, hi.preservesCofiber⟩
    homInvIso := e.homInvIso
    invHomIso := e.invHomIso }

/-- 同値の順射は、元の先行列と最後の辺への制限そのもの。 -/
lemma weakStringTailEquivalence_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringTailEquivalence q n).hom.val = weakStringTailRestriction q n := rfl

/-- 元の全 W 列から貼り合わせへの制限は、全正有限反復で局所化同型。 -/
theorem weakStringTail_multiRealization_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakStringTailEquivalence q n).hom)) :=
  multiRealization_map_localized_isIso_of_equivalence r (weakStringTailEquivalence q n)

end SerrePositivity.KST.Fibration
