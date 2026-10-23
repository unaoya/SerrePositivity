module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitTriangleRawLastPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTransportPointIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransportRightPrism

/-!
概要：元の定値余極限辺の輸送証拠の一点 prism を、元の指定変換の実 prism へ戻す。
方針：元の raw 区間の定値変換表示と同じ普遍証拠への係数代入を使う。
規約：元の実 prism と全初期値を保持。使われ方：全三角形の最後辺の指定比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (b : SSet.Homotopy G J) {C : SSet.{u + 1}}
  (s : C ⟶ leftUnstraightening (coherentColimitRawConstantDiagram B G))
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "cb" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 元の指定辺の定値輸送の一点 prism は、元の同じ全初期値の実 prism そのもの。 -/
lemma coherentColimitConstantTransport_point_prism :
    (Δ[1] ◁ lift s (SSet.const l)) ≫
      (constantDiagramTransportWitness
        (constantDiagramMappingFamilyWitness ((SSet.uliftFunctor.{u + 1, u}).obj B) A)).prism =
    functorHomotopyPointedPrism cb s := by
  dsimp only [coherentColimitRawConstantDiagram] at s ⊢
  change (Δ[1] ◁ lift s (SSet.const l)) ≫
    (constantDiagramMappingFamilyWitness ((SSet.uliftFunctor.{u + 1, u}).obj B) A).leftPrism = _
  have hc := (coherentColimitRawIntervalVertex_constant B b).trans
    (SSet.yonedaEquiv_symm_zero (coherentVertexOfHomotopy cb))
  rw [UnstraighteningFamilyWitness.leftPrism, constantDiagramMappingFamilyWitness_prism]
  have hp := congrArg (fun t =>
    ((Δ[1] ◁ 𝟙 (leftUnstraightening (SSet.const
      (JoinCocone.vertex (coherentDiagramTotalCocone G)) :
        (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))) ⊗ₘ t) ≫
      leftUnstraighteningTransformationFamilyLift
        (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone G)))
        (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone J)))) hc
  rw [hp]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
