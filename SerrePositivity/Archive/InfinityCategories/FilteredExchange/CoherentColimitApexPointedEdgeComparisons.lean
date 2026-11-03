module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedFaceIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyFaces

/-!
概要：元の同じ全三角形比較の三面を、元の第一・最後・長辺の実 prism へ同定する。
方針：正の面の全族の等式と、元の普遍三角形の厳密な二辺の式を使う。
規約：最後辺の始点と全反転 Hom 係数を変えない。
使われ方：二三角形と指定 path の境界比較の同時照合。
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

/-- 第一辺の全比較は、元の第一普遍 prism と元の面の明示的な族を結ぶ。 -/
def coherentColimitApexPointedFirstIso :=
  relativeVertexIsoOfEq pointedSpaceProjection (coherentColimitApexPointedFaceIso B T 2)
    rfl (spaceSimplexPointedFamily_positive_face s (1 : Fin 2))
    (coherentColimitRawUniversalTrianglePrism_first B T q)

/-- 最後辺の全比較は、元の第一輸送後の同じ最後普遍 prism を保持する。 -/
def coherentColimitApexPointedLastIso :=
  relativeVertexIsoOfEq pointedSpaceProjection (coherentColimitApexPointedFaceIso B T 0)
    rfl rfl (coherentColimitRawUniversalTrianglePrism_last B T q)

/-- 長辺の全比較は、元の面の明示的な族と元の全普遍三角形の長辺を結ぶ。 -/
def coherentColimitApexPointedLongIso :=
  relativeVertexIsoOfEq pointedSpaceProjection (coherentColimitApexPointedFaceIso B T 1)
    rfl (spaceSimplexPointedFamily_positive_face s (0 : Fin 2)) rfl

/-- 第一辺の表示を揃えても、同じ全比較の第一面の指定値そのもの。 -/
lemma coherentColimitApexPointedFirstIso_heq :
    HEq (coherentColimitApexPointedFirstIso B T) (coherentColimitApexPointedFaceIso B T 2) :=
  relativeVertexIsoOfEq_heq _ _ _ _ _ _ _

/-- 最後辺も、同じ全比較の第零面の指定値そのもの。 -/
lemma coherentColimitApexPointedLastIso_heq :
    HEq (coherentColimitApexPointedLastIso B T) (coherentColimitApexPointedFaceIso B T 0) :=
  relativeVertexIsoOfEq_heq _ _ _ _ _ _ _

/-- 長辺も、同じ全比較の長辺の面の指定値そのもの。 -/
lemma coherentColimitApexPointedLongIso_heq :
    HEq (coherentColimitApexPointedLongIso B T) (coherentColimitApexPointedFaceIso B T 1) :=
  relativeVertexIsoOfEq_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
