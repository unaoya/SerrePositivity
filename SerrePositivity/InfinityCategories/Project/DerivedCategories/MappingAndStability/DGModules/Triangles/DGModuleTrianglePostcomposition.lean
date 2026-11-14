module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleExt

/-! # dg 加群の合成三角形への後合成

概要：二辺と次数 −1 の成分を閉 dg 加群射で後合成する。
方針：全 Hom end の Leibniz 則と閉零成分の微分零を使う。
規約：全 Hom end の成分を保持。使われ方：β3 の双対比較三単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
variable (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
variable (t : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y) (-1))
variable (ht : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Y)).d (-1) 0 t =
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a ≫ b))).val -
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) c)).val)
variable (q : Y ⟶ Z)

include ht

/-- 閉 dg 加群射で後合成した成分の微分。 -/
lemma dgModuleTriangle_postcompose_differential :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).d (-1) 0
      (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).val t
        (add_zero (-1))) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a ≫ (b ≫ q)))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (c ≫ q))).val := by
  have hq : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).val = 0 :=
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).property
  have ht' : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A t =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a ≫ b))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) c)).val := ht
  change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
    (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).val t
      (add_zero (-1))) = _
  rw [differential_compose, hq, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  simp only [Int.negOnePow_zero, one_smul, zero_add]
  rw [ht', _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp A D (a ≫ b) q,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp A D c q, Category.assoc]

/-- 二辺とホモトピーを閉 dg 加群射で後合成した二単体。 -/
def postcomposeDGModuleTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a (b ≫ q) (c ≫ q)
    (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).val t
      (add_zero (-1))) (dgModuleTriangle_postcompose_differential A D a b c t ht q)).simplex

end SerrePositivity.InfinityCategories.Project.DerivedCategories
