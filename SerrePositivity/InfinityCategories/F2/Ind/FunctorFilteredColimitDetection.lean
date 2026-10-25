module

public import SerrePositivity.InfinityCategories.F2.Ind.FunctorFilteredColimits

/-!
概要：Ind 関手圏の指定 filtered 余極限は、任意の形状制限後も点ごとに余極限。
方針：構成済みの点ごとの余極限との差を全余錐の同型で各評価へ運ぶ。
規約：指定された元の全余錐を使い、頂点だけを同型に置き換えない。
使われ方：単一 filtered 表示の形状同型による移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の指定 filtered 全余錐は、全ての点で余極限である。 -/
lemma indFunctor_isPointwiseColimit_of_isColimit (κ : Cardinal.{u})
    {I C : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I] [Quasicategory C]
    {K : SSet.{u + 1}}
    {p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ (ihom K).obj (IndInfinity κ C)}
    (c : JoinCocone p) (hc : IsColimitCone c) : IsPointwiseColimitCone c := by
  obtain ⟨d, hd, hp, _⟩ := exists_indFunctor_kappaFiltered_colimit κ p
  intro k
  exact (hp k).of_vertexIso (VertexIso.map (colimitConeIso d c hd hc)
    (sliceUnderPostcomp p (evaluateFunctorAt k)))

end SerrePositivity.InfinityCategories.F2.Ind
