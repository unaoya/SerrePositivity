module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentConstantTriangleLargeComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoDownHorizontal

/-!
概要：元の三角形の大きい比較の端点表示を、指定第二辺の表現因子だけへ分配する。
方針：等式による同型の表示変更の合成則を使う。
規約：元の二因子と指定値を保持。使われ方：上面の指定外側因子の分離。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (z : SpaceInfinity.{u} _⦋0⦌)
  (a : smallLeftUnstraightening G ⟶ (spaceInfinityObject z).obj)
  (R : CoherentConstantRepresentation G z a)
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G (SSet.const z) t R.1)

/-- 元の三角形の大きい比較は、同じ三角形比較と指定表現因子の表示変更の合成。 -/
lemma coherentConstantTriangleLargeComparison_eq_factors
    (hlift : (leftUnstraighteningMappingVertexMap F G t).val ≫
      ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map a) =
      (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap F G t ≫ a)) :
    coherentConstantTriangleLargeComparison F G z a R t T =
      (unstraighteningTriangleVertexIso F G (SSet.const z) t R.1 T.diagonal
        T.diagram T.first T.second T.long).postcomp
          (constantUnstraighteningFiberProjection _ z ≫ (pointedSpaceFiberValueEquivalence z).hom)
        ≪≫ functorIsoOfEq ((CoherentConstantRepresentation.largeIso G z a R).precomp
          (leftUnstraighteningMappingVertexMap F G t).val) rfl hlift := by
  rfl

end SerrePositivity.InfinityCategories.F2
