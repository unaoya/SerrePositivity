module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSourceTriangleComponents
public import SerrePositivity.DifferentialGraded.Module.ConeRotation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberFiberEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberSquare

/-! # 標準 cofiber から標準 fiber 錐への比較三単体

概要：二脚とホモトピーを保つ比較射から上下の比較三単体を作る。
方針：標準 fiber 三角形に前合成し、元の cofiber 三角形との一致を検証する。
規約：全 Hom end の dg 加群 nerve 上で構成。使われ方：β3 の錐比較辺の貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
/-- 比較三単体に使う型を固定した閉零成分。 -/
def dgModuleCofiberFiberComparisonCycle (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLiftElement A D f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLiftElement_closed A D f⟩

/-- 三単体の閉成分は実閉加群射の成分に等しい。 -/
lemma dgModuleCofiberFiberComparisonCycle_eq (f : M ⟶ N) :
    dgModuleCofiberFiberComparisonCycle A D f =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)) := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_cycle A D f).symm

/-- 実比較による前合成は元の標準 cone の下三角形。 -/
lemma dgModuleCofiberFiberLower_precompose (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex
      (dgModuleCofiberFiberComparisonCycle A D f) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D f).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceTriangle_obj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleObj, Fin.cases_succ]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge01]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge01]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_projection_element A D f
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceTriangle_edge12]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge12]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge02]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge02]
    rw [moduleHomCycle_zero, moduleHomCycle_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_triple]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_triple]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_nullHomotopy_element A D f

/-- 実比較による前合成は元の標準 cone の上三角形。 -/
lemma dgModuleCofiberFiberUpper_precompose (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex
      (dgModuleCofiberFiberComparisonCycle A D f) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D f).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceTriangle_obj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleObj, Fin.cases_succ]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge01]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge01]
    rw [moduleHomCycle_zero, moduleHomCycle_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceTriangle_edge12]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge12]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge02]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_edge02]
    rw [moduleHomCycle_zero, moduleHomCycle_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  · apply heq_of_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_triple]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_triple]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _

/-- 下側の二つの三角形を結ぶ比較三単体。 -/
def dgModuleCofiberFiberComparisonLower (f : M ⟶ N) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex
    (dgModuleCofiberFiberComparisonCycle A D f)

/-- 上側の二つの三角形を結ぶ比較三単体。 -/
def dgModuleCofiberFiberComparisonUpper (f : M ⟶ N) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex
    (dgModuleCofiberFiberComparisonCycle A D f)

/-- 下側比較の零面は標準 fiber の下三角形。 -/
lemma dgModuleCofiberFiberComparisonLower_face_zero (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonLower A D f).pullback (SimplexCategory.δ (0 : Fin
      4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_zero _ _

/-- 下側比較の一面は元の cofiber の下三角形。 -/
lemma dgModuleCofiberFiberComparisonLower_face_one (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonLower A D f).pullback (SimplexCategory.δ (1 : Fin
      4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D f).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_one _ _).trans (dgModuleCofiberFiberLower_precompose A D f)

/-- 上側比較の零面は標準 fiber の上三角形。 -/
lemma dgModuleCofiberFiberComparisonUpper_face_zero (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonUpper A D f).pullback (SimplexCategory.δ (0 : Fin
      4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_zero _ _

/-- 上側比較の一面は元の cofiber の上三角形。 -/
lemma dgModuleCofiberFiberComparisonUpper_face_one (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonUpper A D f).pullback (SimplexCategory.δ (1 : Fin
      4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D f).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_one _ _).trans (dgModuleCofiberFiberUpper_precompose A D f)

/-- 比較三単体は始域・fiber・cofiber の共通三角形で一致する。 -/
lemma dgModuleCofiberFiberComparison_common (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonLower A D f).pullback (SimplexCategory.δ (2 : Fin
      4)).toOrderHom =
      (dgModuleCofiberFiberComparisonUpper A D f).pullback (SimplexCategory.δ (2 : Fin
        4)).toOrderHom := by
  have hd :
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).d₁.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A
      D (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f)).d₁.symm
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        (dgModuleCofiberFiberComparisonCycle A D f) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_face_two _ _
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        (dgModuleCofiberFiberComparisonCycle A D f) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_congr hd (heq_of_eq rfl)
    _ = _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_face_two _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
