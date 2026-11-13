module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorClosedCycles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom

/-! # 指定 Hom 鎖同型による実閉三角形の持ち上げ
概要：元の三閉射を固定し、標的の比較原始元を実 Hom 同型で戻して二単体を作る。
方針：同じ鎖同型で微分式を反映し、元の閉零 cycle の像との一致を使う。
規約：三頂点・三辺・原始元を保持。使われ方：二軸 cofiber の元の dg nerve への反映。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {E : Type w} [DGCategory R E] (F : DGFunctor R C E)
  {X Y Z : ClosedCategory R C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
  (e : homObject R C X Z ≅ homObject R E (F.onClosed.obj X) (F.onClosed.obj Z))
  (he : e.hom = F.map X Z)
  (t : GradedHom R (F.onClosed.obj X) (F.onClosed.obj Z) (-1))
  (ht : (homObject R E (F.onClosed.obj X) (F.onClosed.obj Z)).d (-1) 0 t =
    (closedHomEquiv R E _ _ (F.onClosed.map (f ≫ g))).val -
      (closedHomEquiv R E _ _ (F.onClosed.map h)).val)

include he ht in
/-- 同じ Hom 鎖同型の逆で戻した原始元は、元の三閉射の微分式を満たす。 -/
lemma dgClosedTriangleHomIsoLift_boundary :
    differential R (e.inv.f (-1) t) =
      compose R (closedHomEquiv R C Y Z g).val (closedHomEquiv R C X Y f).val
        (zero_add 0) - (closedHomEquiv R C X Z h).val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp]
  apply (ModuleCat.mono_iff_injective (e.hom.f 0)).mp inferInstance
  have hc := ConcreteCategory.congr_hom (e.hom.comm (-1) 0) (e.inv.f (-1) t)
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun k => k.f (-1)) e.inv_hom_id) t
  change e.hom.f (-1) (e.inv.f (-1) t) = t at hi
  have hh : e.hom.f 0 (differential R (e.inv.f (-1) t)) = differential R t := by
    exact hc.symm.trans (congrArg (differential R) hi)
  rw [hh, map_sub, he]
  exact ht.trans (congrArg₂ (fun a b => a - b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F (f ≫ g)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F h).symm)

/-- 元の三閉射と戻した同じ原始元を持つ、実 dg nerve 二単体の合成構造。 -/
def dgClosedTriangleHomIsoLift :
    SSet.Truncated.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C h) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compStructOfHomotopy _ _ _ (e.inv.f (-1) t)
  exact dgClosedTriangleHomIsoLift_boundary F f g h e he t ht

/-- 持ち上げた二単体の元の原始元は、指定鎖同型の逆像そのもの。 -/
lemma dgClosedTriangleHomIsoLift_triple :
    (dgClosedTriangleHomIsoLift F f g h e he t ht).simplex.toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = e.inv.f (-1) t := rfl

end SerrePositivity.KST.SConstruction
