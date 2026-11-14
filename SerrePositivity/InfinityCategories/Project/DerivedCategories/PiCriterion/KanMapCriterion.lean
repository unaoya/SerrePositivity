module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents

/-!
概要：空の空間を含む Kan 射の同値性を、π₀ と全基点の正次数 π で判定する。
方針：零次数を明示して既存の全次数 Whitehead 判定に渡す。
規約：KanHomotopyGroup の添字 n は実際の次数 n+1。
使われ方：全空間から候補頂点への射の filtered 余極限判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra
variable {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]

/-- π₀ の全単射性と全基点の正次数の全単射性。空の始域にも意味を持つ。 -/
def KanMapPiCriterion (f : X ⟶ Y) : Prop :=
  Function.Bijective (mapπ₀ f) ∧ ∀ (x : X _⦋0⦌) (n : ℕ),
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) f (x := x) rfl)

/-- 明示的な正次数の条件を、既存の零次数を含む条件へ移す。 -/
lemma KanMapPiCriterion.kanPiIsomorphism {f : X ⟶ Y} (h : KanMapPiCriterion f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  intro x n
  cases n with
  | zero => exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.map_bijective_iff_piZero f (x := x) rfl).mpr h.1
  | succ n => exact h.2 x n

/-- Kan 射の同値性と π 判定。π₀ を別に要求することで空の場合も含む。 -/
lemma homotopyEquivalence_iff_kanMapPiCriterion (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f ↔ KanMapPiCriterion f := by
  constructor
  · intro h
    refine ⟨h.mapPiZero_bijective, fun x n ↦ ?_⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence f h x (n + 1)
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective
      f h.kanPiIsomorphism h.1.surjective

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
