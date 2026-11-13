module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberSquare
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-! # dg 加群の双対比較三単体

概要：標準 cone の二三角形から標準 fiber の二三角形への実比較を作る。
方針：降下比較による後合成を三次内部ホーンで表し、全ての面を照合する。
規約：全 Hom end の実ホモトピーを保持。使われ方：β3 の coslice 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 標準 cone の左包含が満たす合成三角形の微分式。 -/
lemma dgModuleConeTriangle_differential (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).d (-1) 0
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (f ≫ _root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (0 : M ⟶ _root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).val := by
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCycle_zero, sub_zero]
  exact _root_.SerrePositivity.DifferentialGraded.moduleConeInlElement_d A D f

/-- 下側の標準 cone 三角形と fiber 三角形を結ぶ実三単体。 -/
def dgModuleFiberCofiberComparisonLower (f : M ⟶ N) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)
    (moduleConeInr A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) 0
    (moduleConeInlElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
    (dgModuleConeTriangle_differential A D _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f)

/-- 上側の零三角形を結ぶ実三単体。 -/
def dgModuleFiberCofiberComparisonUpper (f : M ⟶ N) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D
    (0 : ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) ⟶ moduleZero A D)
    (0 : moduleZero A D ⟶ moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) 0 0
    (by rw [zero_comp, sub_self]; exact map_zero _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f)

/-- 下側比較の三面は標準 cone の下三角形。 -/
lemma dgModuleFiberCofiberComparisonLower_face_three (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

/-- 上側比較の三面は標準 cone の上三角形。 -/
lemma dgModuleFiberCofiberComparisonUpper_face_three (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

/-- 比較三単体の一面は共通の対角と降下射の厳密三角形。 -/
lemma dgModuleFiberCofiberComparison_common (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (dgModuleFiberCofiberComparisonUpper A D f).pullback
        (SimplexCategory.δ (1 : Fin 4)).toOrderHom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).symm

/-- 下側比較の欠けた面は元の fiber の下三角形。 -/
lemma dgModuleFiberCofiberComparisonLower_face_two (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D f).simplex := by
  unfold dgModuleFiberCofiberComparisonLower
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_two]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeDGModuleTriangle
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_obj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleObj]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge01, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge12, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc_inr]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge02, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle, zero_comp]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_triple, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc_inl A D f

/-- 上側比較の欠けた面は元の fiber の上三角形。 -/
lemma dgModuleFiberCofiberComparisonUpper_face_two (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D f).simplex := by
  unfold dgModuleFiberCofiberComparisonUpper
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_two]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeDGModuleTriangle
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_obj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleObj]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge01, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge12, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, zero_comp]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge02, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, zero_comp]
  · apply heq_of_eq
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_triple, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
