module

public import SerrePositivity.InfinityCategories.F2.VertexConeIsoTransport
public import SerrePositivity.InfinityCategories.F2.FunctorPointwiseColimitCriterion

/-!
概要：同じ元の図式の点ごとの余極限余錐を替えても、完成後の全錐の極限性は同値。
方針：関手圏の余極限余錐の一意性を元の全錐の頂点同型へ写す。
規約：二つの指定余錐を保持。使われ方：選んだ余極限模型から元の指定余錐への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ図式の二つの点ごとの余極限余錐の、元の全余錐の関手同型。 -/
def pointwiseColimitCoconeFunctorIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c d : JoinCocone p)
    (hc : IsPointwiseColimitCone c) (hd : IsPointwiseColimitCone d) :
    FunctorIso c.val d.val :=
  coconeFunctorIsoOfVertexIso c d (colimitConeIso c d (isColimitCone_of_pointwise c hc)
    (isColimitCone_of_pointwise d hd))

/-- 同じ図式の二つの元の点ごとの余極限余錐の、元の頂点どうしの同型。 -/
def pointwiseColimitConeVertexIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c d : JoinCocone p)
    (hc : IsPointwiseColimitCone c) (hd : IsPointwiseColimitCone d) :
    VertexIso c.vertex d.vertex :=
  VertexIso.map (colimitConeIso c d (isColimitCone_of_pointwise c hc)
    (isColimitCone_of_pointwise d hd)) (sliceUnderProjection p)

/-- 同じ元の図式の点ごとの余極限余錐を替えても、完成後の全錐の極限性は同値。 -/
lemma pointwiseColimitCompletedLimit_iff {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X} (c d : JoinCocone p)
    (hc : IsPointwiseColimitCone c) (hd : IsPointwiseColimitCone d) :
    IsLimitCone (functorVertexCone c.vertex) ↔ IsLimitCone (functorVertexCone d.vertex) :=
  isLimitCone_functorVertexCone_iff_of_vertexIso (pointwiseColimitConeVertexIso c d hc hd)

end SerrePositivity.InfinityCategories.F2
