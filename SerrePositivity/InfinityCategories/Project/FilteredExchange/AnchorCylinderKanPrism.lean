module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalEndpointPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.AnchorCylinderCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteAnchorCylinder
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanPrismExtension

/-!
概要：有限因子分解の新しい単射な境界への補正を Kan 模型の円柱で実現する。
方針：元の境界を新しい円柱の終点へ動かす部分円柱を全形状へ延長する。
規約：全円柱の始点と部分円柱を厳密に保持する。
使われ方：境界の単射性を保つ相対有限近似。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の Kan 射の境界を新しい単射な境界へ動かす全円柱。
方針：単位の自然性で部分円柱の始点を合わせ、Kan 標的の部分円柱延長を使う。
規約：有限性はこの延長自体には不要。使われ方：有限な単射境界の補正。 -/
lemma anchorCylinder_kan_prism {A K L : SSet.{u}} (i : A ⟶ K) [Mono i] (a : A ⟶ L)
    (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj L)
    (h : i ≫ r = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app L) :
    ∃ R : K ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a),
      SSet.ι₀ ≫ R = r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
        (pushout.inr (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a) ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ R =
        pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a) := by
  let j := pushout.inr (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a
  let t := pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a
  have hn : j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map j :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality j
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kan_prism_extension i (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map j)
    (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a))
  rw [← Category.assoc, show SSet.ι₀ ≫ t = a ≫ j from _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder_prism_zero a,
    Category.assoc, hn, ← Category.assoc, ← h, Category.assoc]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
