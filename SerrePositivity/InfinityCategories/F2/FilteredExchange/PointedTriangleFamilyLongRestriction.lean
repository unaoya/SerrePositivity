module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFamilyReassociate
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleLongPrismRestriction

/-!
概要：全族の元の pointed 三角形比較を、長辺の同じ始点固定の可縮な prism 空間へ移す。
方針：全係数への結合子移送の後で既存の長辺制限を再利用する。
規約：元の指定比較と全パラメータを保持。使われ方：長辺の三証拠の指定比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
local notation "b₂" => Iso.inv (α_ Δ[2] E K) ≫
  ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D
local notation "v" => Iso.inv (α_ Δ[0] E K) ≫
  PointedTransportPrismFamily.boundary D

/-- 元の全長辺・全初期値を固定する、全係数 E⊗K の prism の選択空間。 -/
def pointedTriangleFamilyLongChoice :=
  relativeFunctorExtensionSpace pointedSpaceProjection
    ((stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ b₂) (prismEndpoint 0 (E ⊗ K))
    (simplexPrismVertex 0 0 (E ⊗ K) ≫ v)
    (triangleLongPrism_initial pointedSpaceProjection b₂ v
      (pointedTriangleFamily_reassociated_initial D))

/-- 同じ元の全初期値を持つ長辺 prism の全選択空間は可縮。 -/
lemma pointedTriangleFamilyLongChoice_contractible :
    IsContractibleKan (pointedTriangleFamilyLongChoice D) :=
  triangleLongPrismExtension_contractible pointedSpaceProjection b₂ v
    (pointedTriangleFamily_reassociated_initial D)

/-- 元の全三角形を、同じ全係数の元の長辺 prism へ制限する実際の射。 -/
def pointedTriangleFamilyLongRestriction :
    pointedPrismFamilyFixedChoice D ⟶ pointedTriangleFamilyLongChoice D :=
  pointedTriangleFamilyReassociate D ≫ triangleLongPrismExtensionRestriction
    pointedSpaceProjection b₂ v (pointedTriangleFamily_reassociated_initial D)

/-- 長辺への実制限の頂点は、元の同じ全延長の長辺を表す。 -/
lemma pointedTriangleFamilyLongRestriction_vertex (W : (Δ[2] ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((scaffoldFirstVertex 2 ▷ E) ▷ K) ≫ W = D.boundary)
    (hp : W ≫ pointedSpaceProjection = ((Δ[2] ◁ p) ▷ K) ≫ D.diagram) :
    (((pointedTriangleFamilyLongRestriction D).app (Opposite.op ⦋0⦌)
      (pointedPrismFamilyFixedChoice_vertex D W hb hp)).val).val =
    functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ (α_ Δ[2] E K).inv ≫ W) := rfl

/-- 元の指定比較の長辺の像は、同じ長辺空間の選択済み比較そのもの。 -/
lemma pointedTriangleFamilyLongRestriction_vertexIso
    {x y : (pointedPrismFamilyFixedChoice D) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e (pointedTriangleFamilyLongRestriction D) =
      (pointedTriangleFamilyLongChoice_contractible D).vertexIso
        ((pointedTriangleFamilyLongRestriction D).app (Opposite.op ⦋0⦌) x)
        ((pointedTriangleFamilyLongRestriction D).app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible (pointedTriangleFamilyLongChoice_contractible D) e _

end SerrePositivity.InfinityCategories.F2
