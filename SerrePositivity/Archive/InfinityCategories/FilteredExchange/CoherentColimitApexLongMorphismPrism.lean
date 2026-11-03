module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedLongPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedCoherentMorphismPrism

/-!
概要：元の余極限三角形の実長辺 prism を、元の同じ固定 Kan 射の prism へ戻す。
方針：同じ全 pointed 族の長辺面の等式と、元の Space 辺の厳密な回収を使う。
規約：元の全係数・実 prism を保持。使われ方：長辺の指定普遍比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T

/-- 元の実長辺の全輸送証人は、元の同じ長辺射だけで決まる実 prism そのもの。 -/
lemma coherentColimitApexPointedLongPrism_heq_morphism :
    HEq (coherentColimitApexPointedLongPrism B T)
      (pointedCoherentMorphismPrism (coherentEdgeHom (SpaceInfinity.δ 1 s))) := by
  have h : coherentColimitApexPointedLongPrism B T =
      spaceSimplexPointedFamily (SpaceInfinity.δ 1 s) :=
    spaceSimplexPointedFamily_positive_face s (0 : Fin 2)
  exact (heq_of_eq h).trans (spaceEdgePointedFamily_heq_morphism (SpaceInfinity.δ 1 s))

end SerrePositivity.InfinityCategories.F2
