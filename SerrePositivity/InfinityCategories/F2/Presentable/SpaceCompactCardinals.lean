module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallSpaceCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.CardinalChangeBound

/-!
概要：小さい空間の族に共通する compactness の正則濃度を、任意の上限を超えて構成する。
方針：元の全非退化単体の濃度を同じ宇宙で評価し、実証済みの小さい Kan 空間の compact 性へ適用する。
規約：各空間の compact 性であり、空間 ∞ 圏の小さい生成圏や accessibility 自体はまだ主張しない。
使われ方：空間・前層の compact 生成族の濃度の調整。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 小さい元の空間族は、任意の上限を超える同じ正則濃度に対して全て compact になる。 -/
lemma exists_spaceCompactCardinal_family {ι : Type u}
    (X : ι → SpaceInfinity.{u} _⦋0⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∀ i, Compact.IsKappaCompact.{u, u + 1} μ (X i) := by
  let K : ι → KanObject.{u} := fun i ↦ spaceInfinityObject (X i)
  obtain ⟨μ, hμ, hσ, hK⟩ := exists_regular_cardinalChangeBound_family
    (fun i ↦ Cardinal.mk (K i).obj.N) (max σ Cardinal.aleph0)
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hω : Cardinal.aleph0 < μ := (le_max_right _ _).trans_lt hσ
  refine ⟨μ, hμ, (le_max_left _ _).trans_lt hσ, ?_⟩
  intro i
  have hc := smallKanObject_isKappaCompact hω (K i) (hK i).1
  have hv : (coherentNerveVertex (K i) : SpaceInfinity.{u} _⦋0⦌) = X i :=
    coherentNerveVertex_object (X i)
  exact hv ▸ hc

/-- 元の各小さい空間は、任意の指定上限を超える正則濃度で compact になる。 -/
lemma exists_spaceCompactCardinal (x : SpaceInfinity.{u} _⦋0⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      Compact.IsKappaCompact.{u, u + 1} μ x := by
  obtain ⟨μ, hμ, hσ, h⟩ := exists_spaceCompactCardinal_family (fun _ : ULift.{u} Unit ↦ x) σ
  exact ⟨μ, hμ, hσ, h (ULift.up ())⟩

end SerrePositivity.InfinityCategories.F2.Presentable
