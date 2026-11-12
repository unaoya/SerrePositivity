module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorClosedCycles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleTrianglePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor

/-! # dg 関手による実加群三角形の保存

概要：合成の差の原始元と実二単体を dg 関手で同時に送る。
方針：Hom の chain map と閉零 cycle の比較で微分式を移し、全四成分を照合する。
規約：Hom end の次数 −1 成分を厳密に保持。使われ方：実四角形の関手像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E))
variable {W X Y : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
variable (t : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y) (-1))
variable (ht : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).d (-1) 0 t =
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a ≫ b))).val -
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) c)).val)

include ht

/-- 原始元の像の微分は実閉零射の像の合成の差。 -/
lemma dgModuleTriangle_map_differential :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A E (F.obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W))
      (F.obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y))).d (-1) 0
        ((F.map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).f (-1) t) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (F.onClosed.map a ≫ F.onClosed.map b))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.onClosed.map c))).val := by
  have h := ConcreteCategory.congr_hom
    ((F.map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).comm (-1) 0) t
  change _ = (F.map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).f 0
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).d (-1) 0 t) at h
  rw [ht, map_sub, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle, Functor.map_comp] at h
  exact h

/-- 実三角形の全対象・辺・次数 −1 成分は dg 関手の像と一致する。 -/
lemma dgModuleCompStruct_map :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).simplex.map F =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A E (F.onClosed.map a) (F.onClosed.map b) (F.onClosed.map c)
        ((F.map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).f (-1) t)
        (dgModuleTriangle_map_differential A D E F a b c t ht)).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F a)
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F b)
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle F c)
  · rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
