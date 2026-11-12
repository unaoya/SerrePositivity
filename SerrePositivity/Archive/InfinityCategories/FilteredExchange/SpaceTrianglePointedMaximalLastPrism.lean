module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleLastSimplexEquality
/-!
概要：最大化側の最後辺の実 pointed prism を、元の第一射の係数作用に続く最後射へ揃える。
方針：標準 join 座標で同じ二つの実単体の全 Hom の一致を反映する。
規約：元の全次数の反転 Hom 係数と二辺を保持する。
使われ方：Ncomp の最大化側の指定対角比較を元の二辺評価へ戻す。
-/

@[expose] public section
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject f))
/-- 概要：最大化側の実最後 prism は、同じ全係数の第一射作用に続く元の最後 prism。
方針：同じ実単体を全 Hom の一致で検出する。
規約：元の全係数と全次数を保持。使われ方：指定対角比較の値の回収。 -/
lemma spaceTrianglePointedFamily_maximal_last_prism : (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ spaceSimplexPointedFamily M =
    (Δ[1] ◁ P) ≫ pointedCoherentMorphismPrism g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨p⟩⟩
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso n).inv).mp
  apply SSet.yonedaEquiv.injective
  exact (spaceSimplexPointedFamily_coordinates M
    (stdSimplex.objEquiv t ≫ SimplexCategory.δ 0) p).trans
    ((coherentTriangleLastSimplex_eq s (stdSimplex.objEquiv t) p).trans
      (pointedCoherentMorphismPrism_coordinates g t
        ((SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)).app
          (Opposite.op ⦋n⦌) p)).symm)

end SerrePositivity.InfinityCategories.F2
