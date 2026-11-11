module

public import SerrePositivity.KST.Spectra.TowerKernelLimOneEquiv

/-!
概要：Kan fibration の塔の正次数ホモトピー群の Milnor 完全列を基点付き集合で構成する。
方針：核と lim¹ の全単射の逆を核の包含へ合成し、像・単射性・全射性を計算する。
規約：lim¹ に群構造を要求しない。比較準同型は既存の実際の射影。
使われ方：Goerss–Jardine VIII §1。塔の一般の収束の lim¹ 項。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)

/-- Milnor 完全列の lim¹ から極限のホモトピー群への実際の単射。 -/
def limOneBoundary
    (a : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right))
      r (limitBasepoint X p) :=
  ((kernelLimOneEquiv X p r).symm a).val

/-- Milnor の単射は lim¹ の基点を単位元へ送る。 -/
@[simp]
lemma limOneBoundary_point : limOneBoundary X p r (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  unfold limOneBoundary
  rw [kernelLimOneEquiv_symm_point]
  rfl

/-- lim¹ 項からの射は単射。 -/
lemma limOneBoundary_injective : Function.Injective (limOneBoundary X p r) :=
  Subtype.val_injective.comp (kernelLimOneEquiv X p r).symm.injective

/-- lim¹ 項からの射と通常の極限比較の合成は単位元。 -/
@[simp]
lemma limitGroupComparison_limOneBoundary (a) :
    limitGroupComparison X p r (limOneBoundary X p r a) = 1 :=
  ((kernelLimOneEquiv X p r).symm a).property

/-- Milnor の lim¹ 項の像は、実際の極限比較の核そのもの。 -/
lemma limOneBoundary_range :
    Set.range (limOneBoundary X p r) = (limitGroupComparison X p r).ker := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact limitGroupComparison_limOneBoundary X p r a
  · intro hb
    refine ⟨kernelLimOneEquiv X p r ⟨b, hb⟩, ?_⟩
    unfold limOneBoundary
    rw [Equiv.symm_apply_apply]

/-- Milnor 列の中央での完全性を元ごとに表す。 -/
lemma exists_limOneBoundary_iff (b) :
    (∃ a, limOneBoundary X p r a = b) ↔ limitGroupComparison X p r b = 1 := by
  change b ∈ Set.range (limOneBoundary X p r) ↔ _
  rw [limOneBoundary_range]
  rfl

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
