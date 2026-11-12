module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyMaximum

/-!
概要：区間を第一因子に置く写像円柱の最大値による変形。
方針：標準のパラメータ第一の最大値作用を対称性で移す。
規約：追加の時間は最後の因子。
使われ方：写像円柱から右端への自然な変形を貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：第一因子に時間を持つ円柱の二つの時間を最大値へ畳む。
方針：対称性でパラメータ第一へ移し、既存の最大値作用を合成する。
規約：元の時刻を第一因子、変形の時刻を第三因子とする。
使われ方：写像円柱の右端への変形。 -/
def cylinderMaximumAction (K : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ⊗ K) ⊗ Δ[1] ⟶ Δ[1] ⊗ K :=
  ((β_ (Δ[1] : SSet.{u}) K).hom ▷ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyMaximumAction K ≫ (β_ K (Δ[1] : SSet.{u})).hom

/-- 概要：変形の零端点で円柱の元の射を保つ。
方針：対称性と端点の自然性、最大値作用の零端点を使う。
規約：元の円柱全体を固定する。
使われ方：写像円柱の変形の始点。 -/
lemma cylinderMaximumAction_zero (K : SSet.{u}) :
    (SSet.ι₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ (Δ[1] ⊗ K) ⊗ Δ[1]) ≫
      cylinderMaximumAction K = 𝟙 _ := by
  simp only [cylinderMaximumAction, SSet.ι₀_comp_assoc]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyMaximumAction_second_zero K)]
  exact SymmetricCategory.symmetry _ _

/-- 概要：元の円柱の一端点は変形中も固定される。
方針：一端点を対称性で移し、最大値作用の最初の一端点を使う。
規約：追加の時間によらず元の時刻は一。
使われ方：写像円柱の貼り合わせ条件。 -/
lemma cylinderMaximumAction_fixed_one (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ cylinderMaximumAction K =
      fst K (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := by
  rw [cylinderMaximumAction, ← Category.assoc, ← comp_whiskerRight,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyMaximumAction_first_one K)]
  rfl

/-- 概要：変形の一端点では円柱の全体を元の一端点へ送る。
方針：追加の一端点の自然性と最大値作用の二番目の一端点を使う。
規約：係数 K は保つ。
使われ方：写像円柱の変形の終点。 -/
lemma cylinderMaximumAction_one (K : SSet.{u}) :
    (SSet.ι₁ : (Δ[1] : SSet.{u}) ⊗ K ⟶ (Δ[1] ⊗ K) ⊗ Δ[1]) ≫
      cylinderMaximumAction K = snd (Δ[1] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := by
  simp only [cylinderMaximumAction, SSet.ι₁_comp_assoc]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyMaximumAction_second_one K)]
  rfl

/-- 概要：円柱の最大値による変形は係数 K を保つ。
方針：直積の第二射影の成分を計算する。
規約：二つの時刻を変えても係数は同じ。
使われ方：写像円柱の底への射影を変形中も固定する。 -/
lemma cylinderMaximumAction_snd (K : SSet.{u}) :
    cylinderMaximumAction K ≫ snd (Δ[1] : SSet.{u}) K =
      fst ((Δ[1] : SSet.{u}) ⊗ K) (Δ[1] : SSet.{u}) ≫ snd (Δ[1] : SSet.{u}) K := by
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
