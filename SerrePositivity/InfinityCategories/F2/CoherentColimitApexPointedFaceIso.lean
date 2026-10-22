module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexPointedFamilyComparison
public import SerrePositivity.InfinityCategories.F2.SpaceTrianglePointedFamilyFaceIso

/-!
概要：元の raw 普遍三角形との全比較を、元の三実辺の上で同時に読む。
方針：同じ全比較の三面の底を、元の余極限三角形の同じ面へ厳密に揃える。
規約：第零面も全反転 Hom 係数を保持。使われ方：元の指定比較の境界式の照合。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "A" => spaceSimplexPointedCoefficients s

/-- 元の全比較から得た、元の同じ辺上の指定相対同型。三面を同時に扱う。 -/
def coherentColimitApexPointedFaceIso (j : Fin 3) :=
  spaceTrianglePointedFamilyFaceIso s (coherentColimitRawUniversalTrianglePrism B T q)
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T) j

/-- 元の三実辺へ底を揃えた比較も、同じ全比較の制限そのものの値。 -/
lemma coherentColimitApexPointedFaceIso_heq (j : Fin 3) :
    HEq (coherentColimitApexPointedFaceIso B T j)
      (coherentColimitApexPointedFamilyRestrictionIso B T (stdSimplex.δ j ▷ A)) :=
  spaceTrianglePointedFamilyFaceIso_heq _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
