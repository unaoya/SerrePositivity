module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawConstantEdgeTransport

/-!
概要：元の固定長辺輸送族を元の任意の係数頂点で評価し、同じ元の実 prism を回収する。
方針：同じ係数頂点の挿入後に第一射影を消去する。
規約：普遍輸送を再選択しない。使われ方：全長辺比較の固定比較先の厳密な同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値な全長辺輸送の一点 prism は、元の同じ raw 普遍輸送 prism そのもの。 -/
lemma coherentColimitRawConstantEdgeTransport_point_prism (B : SSet.{u})
    {F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (d : SSet.Homotopy F J) {K L : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (l : L _⦋0⦌) :
    (Δ[1] ◁ lift (𝟙 K) (SSet.const l)) ≫
      (coherentColimitRawConstantEdgeTransport B d f L).prism =
        coherentColimitRawTransportPointPrism B d f := by
  change (Δ[1] ◁ lift (𝟙 K) (SSet.const l)) ≫ (Δ[1] ◁ fst K L) ≫ _ = _
  rw [← Category.assoc, ← whiskerLeft_comp, lift_fst, whiskerLeft_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
