module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangleTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleLongDataEquality

/-!
概要：区間輸送として保持した長辺の全 prism を、元の指定三角形の同じ長辺証拠へ戻す。
方針：三つの全区間族の厳密な一致だけを使って長辺証拠の引数を揃える。
規約：長辺の持ち上げを再選択しない。使われ方：元の三角形比較と下側比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₁" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "V" => coherentTriangleOfFunctorTriangle (coherentColimitConstantTriangle B T)
local notation "A" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))
local notation "R" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))
local notation "C" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B c))

/-- 元の三辺と元の全三角形から得た、元の選択済み長辺証拠。 -/
def coherentColimitConstantTriangleLongWitness :=
  unstraighteningMappingTriangleLongWitness
    (SSet.const z₀ : ((SSet.uliftFunctor.{u + 1, u}).obj B) ⟶ SpaceInfinity)
    (SSet.const z₁) (SSet.const z₃) (SSet.const A) (SSet.const R) (SSet.const C)
    (V).diagram (V).first (V).second (V).long

/-- 長区間の全輸送の prism は、元の定値余極限三角形の元の長辺証拠そのもの。 -/
lemma coherentColimitConstantTriangleLongTransport_prism :
    (coherentColimitConstantTriangleLongTransport B T).prism =
      (coherentColimitConstantTriangleLongWitness B T).leftPrism := by
  have ha := (coherentColimitRawIntervalVertex_constant B a).trans
    (SSet.yonedaEquiv_symm_zero A)
  have hb := (coherentColimitRawIntervalVertex_constant B b).trans
    (SSet.yonedaEquiv_symm_zero R)
  have hc := (coherentColimitRawIntervalVertex_constant B c).trans
    (SSet.yonedaEquiv_symm_zero C)
  unfold coherentColimitConstantTriangleLongTransport constantDiagramTriangleLongTransport
  dsimp only [constantDiagramTransportWitness]
  exact unstraighteningMappingTriangleLongWitness_leftPrism_eq_of_families
    _ _ _ _ _ _ _ _ _ _ ha hb hc _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
