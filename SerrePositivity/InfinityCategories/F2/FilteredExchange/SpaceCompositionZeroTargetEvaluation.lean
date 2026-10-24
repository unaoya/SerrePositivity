module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointNormalized

/-!
概要：零面の同じ指定終点評価を、独立した名前で固定する。
方針：元の評価射の定義と指定比較の像をそれぞれ等式で回収する。
規約：評価射や比較を選び直さない。
使われ方：具体的な延長空間の定義的照合を分離する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "p" => pointedSpaceProjection
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "Kₘ" => EnrichedFunctor.obj M (SimplicialThickening.mk (ULift.up 0))
local notation "β" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι p (coherentNerveVertex K)
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L
local notation "R" => relativeExtensionFiberEndpoint p β i v
  (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s)

/-- 概要：元の零面の指定終点評価。方針：既存の射に名前を与える。
規約：全係数を保つ。使われ方：評価射の表示の照合。 -/
def spaceCompositionZeroTargetEvaluation := R

/-- 概要：同じ評価射の全表示を回収。方針：定義の等式。
規約：射を変更しない。使われ方：明示的な書き換えで展開を分離する。 -/
lemma spaceCompositionZeroTargetEvaluation_eq : spaceCompositionZeroTargetEvaluation s = R := rfl

/-- 概要：最大化側の全族表示でも同じ終点評価。方針：対象成分だけを定義で照合。
規約：射や係数を選び直さない。使われ方：汎用端点補題の実引数を揃える。 -/
lemma spaceCompositionZeroTargetEvaluation_eq_family :
    spaceCompositionZeroTargetEvaluation s =
      relativeExtensionFiberEndpoint p
        (fst Δ[2] (spaceSimplexPointedCoefficients M) ≫ SSet.yonedaEquiv.symm M)
        (scaffoldFirstVertex 2 ▷ spaceSimplexPointedCoefficients M)
        (snd Δ[0] (spaceSimplexPointedCoefficients M) ≫
          pointedCoherentFiberComparison Kₘ ≫ vertexFiberι p (coherentNerveVertex Kₘ))
        (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s) := rfl

/-- 概要：指定終点像の正規化した値。方針：元の終点値照合を同じ射で読む。
規約：指定比較を保持。使われ方：零面の実最後辺の値照合。 -/
lemma spaceCompositionZeroTargetEvaluation_comparison_heq :
    HEq (VertexIso.map (spaceCompositionTetrahedronZeroComparison s)
      (spaceCompositionZeroTargetEvaluation s)) (pointedOppositeTriangleFunctorIso s) := by
  rw [spaceCompositionZeroTargetEvaluation_eq]
  exact spaceCompositionZeroComparison_endpoint_heq_normalized s

end SerrePositivity.InfinityCategories.F2
