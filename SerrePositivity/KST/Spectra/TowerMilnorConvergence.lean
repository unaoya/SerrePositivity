module

public import SerrePositivity.KST.Spectra.TowerMilnorExactness
public import SerrePositivity.KST.Spectra.TowerKernelNullCriterion

/-!
概要：塔のホモトピー群の極限比較が同型となることと lim¹ の消滅の同値。
方針：Milnor の単射から必要性を得て、既存の零障害判定から十分性を得る。
規約：一般の Kan fibration の塔について述べ、Mittag–Leffler 条件を要求しない。
使われ方：Goerss–Jardine VIII §1。塔の収束の正確な lim¹ 判定。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)

/-- 極限比較の単射性は、次次数の lim¹ の消滅と同値。 -/
lemma limitGroupComparison_injective_iff :
    Function.Injective (limitGroupComparison X p r) ↔
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n))) := by
  constructor
  · intro h
    constructor
    intro a b
    apply limOneBoundary_injective X p r
    apply h
    rw [limitGroupComparison_limOneBoundary, limitGroupComparison_limOneBoundary]
  · exact limitGroupComparison_injective_of_limOne_subsingleton X p r

/-- 一般の塔の極限比較の全単射性は、次次数の lim¹ の消滅と同値。 -/
lemma limitGroupComparison_bijective_iff :
    Function.Bijective (limitGroupComparison X p r) ↔
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n))) := by
  constructor
  · intro h
    exact (limitGroupComparison_injective_iff X p r).1 h.1
  · intro h
    exact ⟨(limitGroupComparison_injective_iff X p r).2 h,
      limitGroupComparison_surjective X p r⟩

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
