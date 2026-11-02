module

public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexCone

/-!
概要：全関手余錐の後合成を、同じ各評価と読み戻した全錐に照合する。
方針：内部 Hom の後合成を計算し、元の全射の等号で普遍性を移す。
規約：点ごとの独立した錐に置き換えず、元の全余錐を保持する。
使われ方：Ind 包含と前層評価による filtered 全錐族の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 各評価の後合成像が余極限なら、全余錐の後合成像は点ごとの余極限。 -/
lemma IsPointwiseColimitCone.postcompose {J K X Y : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p) (F : X ⟶ Y)
    (h : ∀ k, IsColimitCone (mapJoinCocone F (evaluateFunctorCocone c k))) :
    IsPointwiseColimitCone (mapJoinCocone ((ihom K).map F) c) := by
  intro k
  exact h k

/-- 全錐の関手頂点の後合成像を読むことと、同じ全錐を後合成することは極限性が同値。 -/
lemma functorVertexCone_postcompose_isLimit_iff {K X Y : SSet.{u}}
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌) (F : X ⟶ Y) :
    IsLimitCone (functorVertexCone
      (((ihom (join (Δ[0] : SSet.{u}) K)).map F).app (Opposite.op ⦋0⦌) v)) ↔
      IsLimitCone (mapJoinCone F (functorVertexCone v)) := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv _ _).surjective v
  apply isLimitCone_iff_of_diagram_eq
  · rfl
  · rfl

end SerrePositivity.InfinityCategories.F2
