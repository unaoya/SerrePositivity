module
public import SerrePositivity.KST.SConstruction.DGClosedTriangleHomIsoLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleTriangleFunctor

/-! # 同じ全 Hom 持ち上げの加群二単体の回収
概要：元の三閉射を固定した持ち上げは、指定した標的加群二単体を厳密に回収する。
方針：三辺の閉零 cycle と、次数 −1 原始元の同型逆律を全成分で照合する。
規約：有限二単体の対象宇宙を独立に保持。使われ方：二軸 cofiber の二セルの持ち上げ。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {D : Type w} [DGCategory R D] [Small.{u} D] (F : DGFunctor R C (RightModule R D))
  {X Y Z : ClosedCategory R C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
  (e : homObject R C X Z ≅
    homObject R (RightModule R D) (F.onClosed.obj X) (F.onClosed.obj Z))
  (he : e.hom = F.map X Z)
  (t : GradedHom R (F.onClosed.obj X) (F.onClosed.obj Z) (-1))
  (ht : (homObject R (RightModule R D) (F.onClosed.obj X) (F.onClosed.obj Z)).d (-1) 0 t =
    (closedHomEquiv R (RightModule R D) _ _ (F.onClosed.map (f ≫ g))).val -
      (closedHomEquiv R (RightModule R D) _ _ (F.onClosed.map h)).val)

include ht in
/-- 元の閉射の合成保存により、同じ原始元は実加群三角形の微分式を満たす。 -/
lemma dgClosedTriangleHomIsoLiftModule_boundary :
    (homObject R (RightModule R D) (F.onClosed.obj X) (F.onClosed.obj Z)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (F.onClosed.map f ≫ F.onClosed.map g))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (F.onClosed.map h))).val := by
  have hh := ht
  rw [Functor.map_comp] at hh
  exact hh

/-- 元の三閉射を持つ持ち上げの像は、指定加群二単体そのもの。 -/
lemma dgClosedTriangleHomIsoLift_map_module :
    (dgClosedTriangleHomIsoLift F f g h e he t ht).simplex.map F =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (F.onClosed.map f) (F.onClosed.map g) (F.onClosed.map h) t
        (dgClosedTriangleHomIsoLiftModule_boundary F f g h t ht)).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F f)
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F g)
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F h)
  · have hi := ConcreteCategory.congr_hom
      (congrArg (fun k => k.f (-1)) e.inv_hom_id) t
    change e.hom.f (-1) (e.inv.f (-1) t) = t at hi
    rw [he] at hi
    exact heq_of_eq hi

end SerrePositivity.KST.SConstruction
