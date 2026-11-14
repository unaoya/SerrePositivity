module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalEndpointPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.AnchorCylinderCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.AnchorCylinderKanPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiniteAnchorCylinder

/-!
概要：有限因子分解を新しい単射境界へ補正し、元の境界上では全ホモトピーを固定する。
方針：補正円柱の終点を取り、元の因子分解先への射影を合成する。
規約：元の射との比較は実際のホモトピー、境界上では時間に定値。
使われ方：非単射な有限因子分解を相対持ち上げに使える形へ置き換える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：新しい単射境界を保つ Kan 射と、元の境界を固定した比較ホモトピー。
方針：全補正円柱を射影し、単位の自然性で境界上の定値性を計算する。
規約：有限性はこの補正自体に不要。使われ方：有限な単射境界の相対近似。 -/
lemma anchorCylinder_kan_correction {A K L : SSet.{u}} (i : A ⟶ K) [Mono i] (a : A ⟶ L)
    (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj L)
    (h : i ≫ r = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app L) :
    ∃ v : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a),
      i ≫ v = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderIn a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a) ∧
      ∃ H : SSet.Homotopy r (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)),
        (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
          fst A (Δ[1] : SSet.{u}) ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app L := by
  obtain ⟨R, h₀, hR⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder_kan_prism i a r h
  let v := SSet.ι₁ ≫ R
  have hv : i ≫ v = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderIn a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a) := by
    dsimp only [v]
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hR, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder_prism_one]
  let H : SSet.Homotopy r (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)) := {
    h := R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)
    h₀ := by
      change SSet.ι₀ ≫ (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)) = r
      rw [← Category.assoc, h₀, Category.assoc, ← CategoryTheory.Functor.map_comp,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder_section_out, CategoryTheory.Functor.map_id, Category.comp_id]
    h₁ := by
      change SSet.ι₁ ≫ (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)) = v ≫ _
      exact (Category.assoc _ _ _).symm
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  refine ⟨v, hv, H, ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫
    (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)) = _
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app L :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a)).symm
  rw [← Category.assoc, hR, Category.assoc, hn, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinder_prism_out, Category.assoc]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
