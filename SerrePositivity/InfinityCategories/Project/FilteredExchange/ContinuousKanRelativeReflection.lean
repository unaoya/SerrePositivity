module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanStrongRetraction

/-!
概要：Kan 置換内の指定図式を元の Kan 対象へ、指定境界と全比較円柱を保って戻す。
方針：単位の厳密な左逆を適用し、単位の像を固定する変形円柱を前合成する。
規約：境界射の単射性や形状の有限性は不要。
使われ方：共通値の Kan 置換内の指定 path を端点固定で元の値へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：置換内の図式は元の指定境界を保って戻り、比較円柱も境界上で定値。
方針：強変形 retract の左逆と全相対円柱を使う。
規約：元の指定図式との実際の比較を返す。使われ方：端点固定の path の反映。 -/
lemma continuousKanReplacement_relative_reflection {A K X : SSet.{u}} [KanComplex X]
    (i : A ⟶ K) (a : A ⟶ X) (z : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X)
    (hz : i ≫ z = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) :
    ∃ v : K ⟶ X, i ≫ v = a ∧
      ∃ G : SSet.Homotopy (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) z,
        (i ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst A (Δ[1] : SSet.{u}) ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X := by
  obtain ⟨r, hr, H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacementUnit_strong_retraction X
  let η : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
  let v := z ≫ r
  have hv : i ≫ v = a := by
    dsimp only [v]
    rw [← Category.assoc, hz, Category.assoc, hr, Category.comp_id]
  let G : SSet.Homotopy (v ≫ η) z :=
    { h := (z ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by
        rw [SSet.ι₀_comp_assoc, H.h₀]
        rfl
      h₁ := by
        rw [SSet.ι₁_comp_assoc, H.h₁, Category.comp_id]
        rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨v, hv, G, ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫ (z ▷ (Δ[1] : SSet.{u})) ≫ H.h = _
  rw [← comp_whiskerRight_assoc, hz, comp_whiskerRight, Category.assoc, hH]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
