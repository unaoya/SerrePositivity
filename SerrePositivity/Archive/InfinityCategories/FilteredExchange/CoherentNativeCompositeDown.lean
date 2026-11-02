module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeNativePathDown
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDown
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoMapTransport

/-!
概要：元の native 二射の合成比較と cospan の指定可換同型を同じ下降関手で表示する。
方針：元の両端を明示して下降し、通常の下降関手による指定像との型付き一致を記録する。
規約：元の指定値を保持。使われ方：四射の値比較の可換式の小宇宙への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
section Composite
variable {B D E : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
  (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
  (b : smallLeftUnstraightening G ⟶ smallLeftUnstraightening H)

/-- 元の二射の合成比較の指定値を元の小宇宙へ下降する。 -/
def coherentTotalMapNativeCompositeDownIso :
    FunctorIso (coherentTotalMapNativeValueDown F G a ≫ coherentTotalMapNativeValueDown G H b)
      (coherentTotalVertexMap F G a ≫ coherentTotalVertexMap G H b) := by
  apply functorIsoDown.{u, u + 1}
  apply functorIsoOfEq (coherentTotalMapNativeCompositeIso F G H a b)
  · rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift]
  · rfl

/-- 下降した合成比較は、同じ元の比較の通常の下降関手による指定像である。 -/
lemma coherentTotalMapNativeCompositeDownIso_heq_map :
    HEq (coherentTotalMapNativeCompositeDownIso F G H a b)
      ((functorSpaceDown.{u, u + 1}
        (spaceInfinityObject (coherentDiagramTotalVertex F)).obj
        (spaceInfinityObject (coherentDiagramTotalVertex H)).obj).mapIso
          (coherentTotalMapNativeCompositeIso F G H a b)) := by
  exact functorIsoDown_ofEq_heq_mapIso
    (f := coherentTotalMapNativeValueDown F G a ≫ coherentTotalMapNativeValueDown G H b)
    (g := coherentTotalVertexMap F G a ≫ coherentTotalVertexMap G H b)
    (coherentTotalMapNativeCompositeIso F G H a b)
    (by rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift]) rfl
end Composite

/-- 元の小宇宙の native 可換同型も、同じ通常の下降関手による元の指定像である。 -/
lemma coherentCospanConeNativePathDownIso_heq_map {B : SSet.{u}} [Quasicategory B]
    (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (C : CoherentTransformationCospanCone F X Y Z) :
    HEq (coherentCospanConeNativePathDownIso F X Y Z C)
      ((functorSpaceDown.{u, u + 1}
        (spaceInfinityObject (coherentDiagramTotalVertex F)).obj
        (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj).mapIso
          (coherentCospanConeNativeValuePathIso F X Y Z C)) := by
  exact functorIsoDown_ofEq_heq_mapIso
    (f := coherentTotalMapNativeValueDown F X (coherentTransformationTotalMap F X C.toLeft) ≫
      coherentTotalMapNativeValueDown X Z (coherentTransformationTotalMap X Z C.fromLeft))
    (g := coherentTotalMapNativeValueDown F Y (coherentTransformationTotalMap F Y C.toRight) ≫
      coherentTotalMapNativeValueDown Y Z (coherentTransformationTotalMap Y Z C.fromRight))
    (coherentCospanConeNativeValuePathIso F X Y Z C)
    (by rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift])
    (by rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift])

end SerrePositivity.InfinityCategories.F2
