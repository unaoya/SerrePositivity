module

public import SerrePositivity.KST.Spectra.TowerHomotopyComparison
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
概要：塔のホモトピー群の整合族の群と、極限からの全射な比較準同型。
方針：各段の群の積の部分群として整合族を定義し、代表による全射性を束ねる。
規約：比較の核を零とは仮定せず、各段で零となる類として記述する。
使われ方：Goerss–Jardine VIII §1。lim¹ の核を解析する比較射。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right]

/-- 各段の正次数ホモトピー群の逆極限を、積の整合族の部分群として表す。 -/
def compatibleGroup (r : ℕ) :
    Subgroup (∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right r (X n).basepoint) where
  carrier a := ∀ n, pointedGroupMap r (p n) (a (n + 1)) = a n
  one_mem' := by intro n; exact map_one _
  mul_mem' ha hb := by
    intro n
    change pointedGroupMap r (p n) (_ * _) = _ * _
    rw [map_mul, ha n, hb n]
  inv_mem' ha := by
    intro n
    change pointedGroupMap r (p n) (_⁻¹) = _⁻¹
    rw [map_inv, ha n]

variable [∀ n, Fibration (p n).right]

/-- 極限のホモトピー類の各射影は塔の群の遷移と整合する。 -/
lemma limitGroupProjection_comp (r n : ℕ)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)) r (limitBasepoint X p)) :
    pointedGroupMap r (p n) (limitGroupProjection X p r (n + 1) b) =
      limitGroupProjection X p r n b := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep b
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) (n + 1))
      rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n)
        rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  change (s.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ (n + 1)) ≫ (p n).right =
    s.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp]

/-- 極限の正次数ホモトピー群から、段ごとの群の逆極限への比較準同型。 -/
def limitGroupComparison (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right))
        r (limitBasepoint X p) →* compatibleGroup X p r where
  toFun b := ⟨fun n ↦ limitGroupProjection X p r n b, fun n ↦ limitGroupProjection_comp X p r n b⟩
  map_one' := by
    apply Subtype.ext
    funext n
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    funext n
    exact map_mul _ _ _

/-- 比較準同型は全射。これは単射性や lim¹ の消滅を含まない。 -/
theorem limitGroupComparison_surjective (r : ℕ) :
    Function.Surjective (limitGroupComparison X p r) := by
  intro a
  obtain ⟨b, hb⟩ := exists_limit_class X p r a.val a.property
  exact ⟨b, Subtype.ext (funext hb)⟩

/-- 比較の核は、全ての段で単位元へ射影される極限の類。 -/
lemma limitGroupComparison_eq_one_iff (r : ℕ)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)) r (limitBasepoint X p)) :
    limitGroupComparison X p r b = 1 ↔ ∀ n, limitGroupProjection X p r n b = 1 := by
  constructor
  · intro h n
    exact congrArg (fun a : compatibleGroup X p r ↦ a.val n) h
  · intro h
    exact Subtype.ext (funext h)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
