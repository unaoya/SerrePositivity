module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOneMittagLeffler
public import SerrePositivity.KST.Spectra.TowerKernelNullCriterion

/-!
概要：Mittag–Leffler 条件と像の安定化による塔のホモトピー群の比較同型。
方針：lim¹ の消滅を既証の零障害判定へ渡し、全射な比較準同型を同型にする。
規約：次のホモトピー次数の像の安定化が入力。骨格の塔でのその証明は別工程。
使われ方：Goerss–Jardine VIII §§1–2。骨格の塔の収束への適用界面。
-/

@[expose] public section
universe u
open CategoryTheory Opposite SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TowerLimOne

variable (G : ℕ → Type u) [∀ n, Group (G n)] (q : ∀ n, G (n + 1) →* G n)

/-- 二つの自然数の間の合成した遷移。 -/
def transitionLE (n m : ℕ) (h : n ≤ m) : G m →* G n :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q (homOfLE h).op

/-- 各段への合成遷移の像の最終的な安定化は Mittag–Leffler 条件を導く。 -/
theorem isMittagLeffler_of_stable_ranges
    (hstable : ∀ n, ∃ m, ∃ hnm : n ≤ m, ∀ k, ∀ hmk : m ≤ k,
      Set.range (transitionLE G q n m hnm) =
        Set.range (transitionLE G q n k (hnm.trans hmk))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler G q := by
  apply (Functor.isMittagLeffler_iff_subset_range_comp _).2
  intro j
  obtain ⟨m, hnm, hm⟩ := hstable j.unop
  refine ⟨op m, (homOfLE hnm).op, fun {k} g ↦ ?_⟩
  have hg : m ≤ k.unop := leOfHom g.unop
  have he : g ≫ (homOfLE hnm).op = (homOfLE (hnm.trans hg)).op := Subsingleton.elim _ _
  rw [he]
  exact (hm k.unop hg).le

end TowerLimOne

namespace PointedFibrationTower

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)

/-- 次のホモトピー次数が Mittag–Leffler な塔では比較準同型は全単射。 -/
theorem limitGroupComparison_bijective_of_mittagLeffler
    (hML : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n))) :
    Function.Bijective (limitGroupComparison X p r) :=
  ⟨limitGroupComparison_injective_of_limOne_subsingleton X p r
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.subsingleton_of_mittagLeffler _ _ hML), limitGroupComparison_surjective X p r⟩

/-- 次のホモトピー次数が Mittag–Leffler な塔の比較群同型。 -/
def limitGroupEquivOfMittagLeffler
    (hML : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right))
      r (limitBasepoint X p) ≃* compatibleGroup X p r :=
  MulEquiv.ofBijective (limitGroupComparison X p r)
    (limitGroupComparison_bijective_of_mittagLeffler X p r hML)

/-- 次の次数の合成遷移の像が安定すれば、比較準同型は全単射。 -/
theorem limitGroupComparison_bijective_of_stable_ranges
    (hstable : ∀ n, ∃ m, ∃ hnm : n ≤ m, ∀ k, ∀ hmk : m ≤ k,
      Set.range (TowerLimOne.transitionLE
        (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
        (fun n ↦ pointedGroupMap (r + 1) (p n)) n m hnm) =
      Set.range (TowerLimOne.transitionLE
        (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
        (fun n ↦ pointedGroupMap (r + 1) (p n)) n k (hnm.trans hmk))) :
    Function.Bijective (limitGroupComparison X p r) :=
  limitGroupComparison_bijective_of_mittagLeffler X p r
    (TowerLimOne.isMittagLeffler_of_stable_ranges _ _ hstable)

end PointedFibrationTower
end
end SerrePositivity.KST.Spectra
