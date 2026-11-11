module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftAnodyneLimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def IsExcisionCorePunctured (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}) : Prop :=
  1 ≤ p.val.val.down.val.1.val + p.val.val.down.val.2.val

abbrev ExcisionCorePuncturedIndex :=
  {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} // IsExcisionCorePunctured p}

def IsExcisionCoreCospan (p : ExcisionCorePuncturedIndex.{u}) : Prop :=
  p.val.val.val.down.val.1.val ≤ 1 ∧ p.val.val.val.down.val.2.val ≤ 1

def excisionCorePuncturedLower :
    ExcisionCorePuncturedIndex.{u} →o ExcisionCorePuncturedIndex.{u} where
  toFun p := by
    let x : Fin 3 := ⟨min p.val.val.val.down.val.1.val 1, by omega⟩
    let y : Fin 3 := ⟨min p.val.val.val.down.val.2.val 1, by omega⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint x y, by
      have hp := p.property
      change 1 ≤ p.val.val.val.down.val.1.val + p.val.val.val.down.val.2.val at hp
      change 1 ≤ min p.val.val.val.down.val.1.val 1 + min p.val.val.val.down.val.2.val 1
      omega⟩
  monotone' := by
    intro a b h
    constructor
    · change min a.val.val.val.down.val.1.val 1 ≤ min b.val.val.val.down.val.1.val 1
      exact min_le_min h.1 le_rfl
    · change min a.val.val.val.down.val.2.val 1 ≤ min b.val.val.val.down.val.2.val 1
      exact min_le_min h.2 le_rfl

lemma excisionCorePuncturedLower_le (p : ExcisionCorePuncturedIndex.{u}) :
    excisionCorePuncturedLower p ≤ p := ⟨Nat.min_le_left _ _, Nat.min_le_left _ _⟩

lemma excisionCorePuncturedLower_mem (p : ExcisionCorePuncturedIndex.{u}) :
    IsExcisionCoreCospan (excisionCorePuncturedLower p) :=
  ⟨Nat.min_le_right _ _, Nat.min_le_right _ _⟩

lemma excisionCorePuncturedLower_fixed (p : ExcisionCorePuncturedIndex.{u})
    (hp : IsExcisionCoreCospan p) : excisionCorePuncturedLower p = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact min_eq_left hp.1
  · exact min_eq_left hp.2

lemma excisionCoreCospan_leftAnodyne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve ExcisionCorePuncturedIndex.{u})
      (fun v ↦ IsExcisionCoreCospan (nerveEquiv v))).ι :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetInterior_leftAnodyne IsExcisionCoreCospan excisionCorePuncturedLower
    excisionCorePuncturedLower_le excisionCorePuncturedLower_mem excisionCorePuncturedLower_fixed

lemma excisionCoreCospan_limit_iff {X : SSet.{u}} [Quasicategory X]
    {F : nerve ExcisionCorePuncturedIndex.{u} ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve ExcisionCorePuncturedIndex.{u})
        (fun v ↦ IsExcisionCoreCospan (nerveEquiv v))).ι) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isLimitCone_iff_restrict_of_leftAnodyne c _ excisionCoreCospan_leftAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
