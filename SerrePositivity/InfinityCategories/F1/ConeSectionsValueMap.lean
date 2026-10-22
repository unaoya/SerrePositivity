module

public import SerrePositivity.InfinityCategories.F1.ConeSectionsMap
public import SerrePositivity.InfinityCategories.F1.CoherentSmallConstantSource

/-!
概要：元の錐の全切断写像を、小さい値と全切断の持ち上げの間の射へ正規化する。
方針：pointed fiber の値の比較と全切断の縮小同型を合成する。
規約：元の全切断写像・指定頂点の等式を保持する。
使われ方：指定恒等射の比較から元の全切断写像の同値性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
local instance : KanComplex (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  HomotopyLimits.simplicialSections_kanComplex (leftUnstraighteningProjection F)

/-- 元の fiber から全切断への射を、小さい値の持ち上げで表示する。 -/
def coneSectionsValueMapAt (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (coherentSpaceSectionsObject F).obj :=
  (pointedSpaceFiberValueEquivalence z).symm.hom ≫ coneSectionsMapAt c z hv ≫
    (smallUnstraighteningSectionsIso F).inv

/-- 縮小した内部 Hom の比較像を戻すと、同じ実際の値の写像の頂点。 -/
lemma coneSectionsValueMapAt_smallComparison (c : JoinCone F)
    (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    (uliftFunctorSpaceIso (spaceInfinityObject z).obj (coherentSpaceSectionsObject F).obj).hom.app
        (Opposite.op ⦋0⦌)
        ((coherentSmallConstantSourceMap F z).app (Opposite.op ⦋0⦌)
          (coneTransformationPointAt c z hv)) = functorVertex (coneSectionsValueMapAt F c z hv) := by
  have h : coherentSmallConstantSourceMap F z ≫
      (uliftFunctorSpaceIso (spaceInfinityObject z).obj (coherentSpaceSectionsObject F).obj).hom =
      coherentConstantSourceMap F z ≫
        ((pointedSpaceFiberValueEquivalence z).symm.precompose
          (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F))).hom ≫
        (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj)).map
          (smallUnstraighteningSectionsIso F).inv := by
    simp only [coherentSmallConstantSourceMap, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have e := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) (coneTransformationPointAt c z hv)) h
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e
  rw [← coneSectionsMapAt_vertex] at e
  exact e

end SerrePositivity.InfinityCategories
