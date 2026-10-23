module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLongMorphismPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismPrismEquality

/-!
概要：元の余極限三角形の全実長辺 prism を、元の同じ反転合成 prism へ一致させる。
方針：元の長辺射への回収と、元の二つの全係数 prism の厳密な一致を合成する。
規約：元の全係数・実 prism を保持。使われ方：同じ指定輸送比較の値の照合。
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

/-- 元の全実長辺 prism は、同じ元の長辺射で制限した元の全反転合成 prism。 -/
lemma coherentColimitApexPointedLongPrism_heq_reverse :
    HEq (coherentColimitApexPointedLongPrism B T)
      (pointedReverseMorphismPrism
        (coherentEdgeHom (SpaceInfinity.δ 1 (coherentColimitApexTriangle B T)))) :=
  (coherentColimitApexPointedLongPrism_heq_morphism B T).trans
    (heq_of_eq (pointedCoherentMorphismPrism_eq_reverse _))

end SerrePositivity.InfinityCategories.F2
