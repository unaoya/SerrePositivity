module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexCone

/-!
概要：任意の形状について、一般 coherent filtered 余極限と極限の交換を定式化する。
方針：錐形状上の関手の族の元の点ごとの余極限余錐を量化する。
規約：余極限関手の選択は不要で、元の全単体を保持。使われ方：有限セル帰納の述語。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 点ごとに filtered 余極限で補完した coherent な錐の族の、極限性の保存。 -/
def CoherentFilteredLimitExchangeShape (K : SSet.{u}) : Prop :=
  ∀ (B : SSet.{u}) [Quasicategory B] [IsFilteredInfinity B]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj
        SpaceInfinity.{u})
    (c : JoinCocone p), IsPointwiseColimitCone c →
      (∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up b)))) →
      IsLimitCone (functorVertexCone c.vertex)

end SerrePositivity.InfinityCategories.F2
