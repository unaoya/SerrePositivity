module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTriangleFamilyLongRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointWitness

/-!
概要：全族の元の pointed 三角形の同じ長辺を、始点固定の実終点付き証拠にする。
方針：結合子と長辺の初期正方形で、元の全初期値と実終点を直接回収する。
規約：全延長を選び直さない。使われ方：三つの元の長辺証拠の指定比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
local notation "b₂" => ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D
local notation "v" => simplexPrismVertex 0 0 (E ⊗ K) ≫ Iso.inv (α_ Δ[0] E K) ≫
  PointedTransportPrismFamily.boundary D

/-- 元の全長辺の始点は、結合子を移した元の同じ全初期値。 -/
lemma pointedTriangleFamilyLong_initial (W : (Δ[2] ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((scaffoldFirstVertex 2 ▷ E) ▷ K) ≫ W = D.boundary) :
    prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫
      (α_ Δ[2] E K).inv ≫ W = v := by
  have hr : (scaffoldFirstVertex 2 ▷ (E ⊗ K)) ≫ (α_ Δ[2] E K).inv ≫ W =
      (α_ Δ[0] E K).inv ≫ D.boundary := by
    rw [← Category.assoc, pointedTriangleFamily_initial_associator, Category.assoc, hb]
  rw [← Category.assoc (prismEndpoint 0 (E ⊗ K)), triangleLongPrism_initial_square]
  simpa only [Category.assoc] using
    congrArg (fun z => simplexPrismVertex 0 0 (E ⊗ K) ≫ z) hr

/-- 元の全三角形の長辺を、元の全初期値・底・実終点を保持した同じ証拠へ束ねる。 -/
def pointedTriangleFamilyLongEndpointWitness
    (W : (Δ[2] ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((scaffoldFirstVertex 2 ▷ E) ▷ K) ≫ W = D.boundary)
    (hp : W ≫ pointedSpaceProjection = b₂)
    {Q : SSet.{u + 1}} (q : Q ⟶ SpaceInfinity.{u}) (a : E ⊗ K ⟶ Q)
    (g : E ⊗ K ⟶ pullback pointedSpaceProjection q)
    (hg : g ≫ pullback.snd pointedSpaceProjection q = a)
    (ht : (simplexPrismVertex 2 2 E ▷ K) ≫ W = g ≫ pullback.fst pointedSpaceProjection q) :
    RelativeExtensionEndpointWitness pointedSpaceProjection
      ((stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ (α_ Δ[2] E K).inv ≫ b₂)
      (prismEndpoint 0 (E ⊗ K)) v (prismEndpoint 1 (E ⊗ K)) q a where
  extension := (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ (α_ Δ[2] E K).inv ≫ W
  over := by rw [Category.assoc, Category.assoc, hp]
  initial := pointedTriangleFamilyLong_initial D W hb
  endpoint := g
  endpoint_over := hg
  evaluate := ht

end SerrePositivity.InfinityCategories.F2
