module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationStabilityDescent
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits

/-! # ∞ 圏同値による安定性と完全性の輸送

概要：任意の quasicategory の同値は安定性を保ち反映し、完全関手である。
方針：可逆 path 置換の二つの自明 Kan fibration と厳密な切断へ分解する。
規約：三角圏の構造から安定性を引き戻さない。使われ方：β3 の dg Yoneda と平坦模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

/-- ∞ 圏同値の両端の安定性は同値。 -/
lemma IsQCatEquivalence.isStable_iff {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := he.equivalencePathReplacementMap_trivialKanFibration
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_iff_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_iff_of_trivialKanFibration q)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsQCatEquivalence (isStable_iff)


/-- 明示的な ∞ 圏同値の両端の安定性は同値。 -/
lemma QCatEquivalence.isStable_iff (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y :=
  e.isQCatEquivalence.isStable_iff

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (isStable_iff)


/-- 任意の ∞ 圏同値は零対象と cofiber 列を保存する完全関手。 -/
lemma isExactFunctor_of_isQCatEquivalence {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := he.equivalencePathReplacementMap_trivialKanFibration
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_section_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f) s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection f)
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (s ≫ q) := inferInstance
  simpa only [s, q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map] using h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
