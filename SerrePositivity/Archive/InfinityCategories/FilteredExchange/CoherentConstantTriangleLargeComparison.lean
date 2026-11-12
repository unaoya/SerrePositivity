module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitRepresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoTargetFactorValue

/-!
概要：指定表現を持つ元の三角形の大きい全空間上の比較を保持する。
方針：元の全三角形の比較と第二辺の指定表現を合成し、持ち上げの等式だけを反映する。
規約：元の指定値を保持。使われ方：三角形表現の縮小と復元での値の回収。
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

/-- 同じ全三角形と元の第二辺の表現から得る、大きい全空間の指定比較。 -/
def coherentConstantTriangleLargeComparison :
    FunctorIso
      ((leftUnstraighteningMappingVertexMap F (SSet.const z) T.diagonal).val ≫
        constantUnstraighteningFiberProjection _ z ≫ (pointedSpaceFiberValueEquivalence z).hom)
      ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap F G t ≫ a)) := by
  have e := (unstraighteningTriangleVertexIso F G (SSet.const z) t R.1 T.diagonal
    T.diagram T.first T.second T.long).postcomp
      (constantUnstraighteningFiberProjection _ z ≫ (pointedSpaceFiberValueEquivalence z).hom)
  have er := (CoherentConstantRepresentation.largeIso G z a R).precomp
    (leftUnstraighteningMappingVertexMap F G t).val
  have hlift : (leftUnstraighteningMappingVertexMap F G t).val ≫
      ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map a) =
      (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap F G t ≫ a) := by
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
      coherentTransformationTotalMap_lift]
  exact e ≪≫ functorIsoOfEq er rfl hlift

/-- 大きい比較の表示変更は、同じ上面と第二辺の表現の比較合成の値を保持する。 -/
lemma coherentConstantTriangleLargeComparison_heq_raw :
    HEq (coherentConstantTriangleLargeComparison F G z a R t T)
      ((unstraighteningTriangleVertexIso F G (SSet.const z) t R.1 T.diagonal
        T.diagram T.first T.second T.long).postcomp
          (constantUnstraighteningFiberProjection _ z ≫ (pointedSpaceFiberValueEquivalence z).hom)
        ≪≫ (CoherentConstantRepresentation.largeIso G z a R).precomp
          (leftUnstraighteningMappingVertexMap F G t).val) := by
  unfold coherentConstantTriangleLargeComparison
  exact functorIso_trans_target_heq _ _ _

end SerrePositivity.InfinityCategories.F2
