module
public import SerrePositivity.InfinityCategories.Derived.DGSourceTriangleComponents
public import SerrePositivity.DifferentialGraded.Module.ConeRotation
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberSquare

/-! # 標準 cofiber から標準 fiber 錐への比較三単体

概要：二脚とホモトピーを保つ比較射から上下の比較三単体を作る。
方針：標準 fiber 三角形に前合成し、元の cofiber 三角形との一致を検証する。
規約：全 Hom end の dg 加群 nerve 上で構成。使われ方：β3 の錐比較辺の貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}
/-- 比較三単体に使う型を固定した閉零成分。 -/
def dgModuleCofiberFiberComparisonCycle (f : M ⟶ N) :
    zeroCycles (homObject A (RightModule A D) (ForgetEnrichment.to (Complex A) M)
      (dgModuleFiber A D (moduleConeInr A D f))) :=
  ⟨dgModuleCofiberFiberLiftElement A D f, dgModuleCofiberFiberLiftElement_closed A D f⟩

/-- 三単体の閉成分は実閉加群射の成分に等しい。 -/
lemma dgModuleCofiberFiberComparisonCycle_eq (f : M ⟶ N) :
    dgModuleCofiberFiberComparisonCycle A D f =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (dgModuleCofiberFiberLift A D f)) := by
  apply Subtype.ext
  exact (dgModuleCofiberFiberLift_cycle A D f).symm

/-- 実比較による前合成は元の標準 cone の下三角形。 -/
lemma dgModuleCofiberFiberLower_precompose (f : M ⟶ N) :
    SourcePrecomposition.simplex
      (dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex
      (dgModuleCofiberFiberComparisonCycle A D f) =
      (dgModuleConeLowerTriangle A D f).simplex := by
  apply dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [dgSourceTriangle_obj, dgModuleFiberLowerTriangle, dgModuleConeLowerTriangle,
        dgModuleCompStruct_obj, HomotopyComparison.tripleObj, Fin.cases_succ]
  · apply heq_of_eq
    rw [sourceTriangle_edge01]
    simp only [dgModuleFiberLowerTriangle, dgModuleConeLowerTriangle,
      dgModuleCompStruct_edge01]
    rw [dgModuleFiberProjection_cycle]
    exact dgModuleCofiberFiberLift_projection_element A D f
  · apply heq_of_eq
    rw [dgSourceTriangle_edge12]
    simp only [dgModuleFiberLowerTriangle, dgModuleConeLowerTriangle,
      dgModuleCompStruct_edge12]
  · apply heq_of_eq
    rw [sourceTriangle_edge02]
    simp only [dgModuleFiberLowerTriangle, dgModuleConeLowerTriangle,
      dgModuleCompStruct_edge02]
    rw [moduleHomCycle_zero, moduleHomCycle_zero, zero_compose]
  · apply heq_of_eq
    rw [sourceTriangle_triple]
    simp only [dgModuleFiberLowerTriangle, dgModuleConeLowerTriangle,
      dgModuleCompStruct_triple]
    exact dgModuleCofiberFiberLift_nullHomotopy_element A D f

/-- 実比較による前合成は元の標準 cone の上三角形。 -/
lemma dgModuleCofiberFiberUpper_precompose (f : M ⟶ N) :
    SourcePrecomposition.simplex
      (dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex
      (dgModuleCofiberFiberComparisonCycle A D f) =
      (dgModuleConeUpperTriangle A D f).simplex := by
  apply dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [dgSourceTriangle_obj, dgModuleFiberUpperTriangle, dgModuleConeUpperTriangle,
        dgModuleCompStruct_obj, HomotopyComparison.tripleObj, Fin.cases_succ]
  · apply heq_of_eq
    rw [sourceTriangle_edge01]
    simp only [dgModuleFiberUpperTriangle, dgModuleConeUpperTriangle,
      dgModuleCompStruct_edge01]
    rw [moduleHomCycle_zero, moduleHomCycle_zero, zero_compose]
  · apply heq_of_eq
    rw [dgSourceTriangle_edge12]
    simp only [dgModuleFiberUpperTriangle, dgModuleConeUpperTriangle,
      dgModuleCompStruct_edge12]
  · apply heq_of_eq
    rw [sourceTriangle_edge02]
    simp only [dgModuleFiberUpperTriangle, dgModuleConeUpperTriangle,
      dgModuleCompStruct_edge02]
    rw [moduleHomCycle_zero, moduleHomCycle_zero, zero_compose]
  · apply heq_of_eq
    rw [sourceTriangle_triple]
    simp only [dgModuleFiberUpperTriangle, dgModuleConeUpperTriangle,
      dgModuleCompStruct_triple]
    exact zero_compose _ _

/-- 下側の二つの三角形を結ぶ比較三単体。 -/
def dgModuleCofiberFiberComparisonLower (f : M ⟶ N) : Simplex A (RightModule A D) 3 :=
  SourcePrecomposition.prepend
    (dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex
    (dgModuleCofiberFiberComparisonCycle A D f)

/-- 上側の二つの三角形を結ぶ比較三単体。 -/
def dgModuleCofiberFiberComparisonUpper (f : M ⟶ N) : Simplex A (RightModule A D) 3 :=
  SourcePrecomposition.prepend
    (dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex
    (dgModuleCofiberFiberComparisonCycle A D f)

/-- 下側比較の零面は標準 fiber の下三角形。 -/
lemma dgModuleCofiberFiberComparisonLower_face_zero (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonLower A D f).pullback (SimplexCategory.δ (0 : Fin
      4)).toOrderHom =
      (dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex :=
  SourcePrecomposition.prepend_face_zero _ _

/-- 下側比較の一面は元の cofiber の下三角形。 -/
lemma dgModuleCofiberFiberComparisonLower_face_one (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonLower A D f).pullback (SimplexCategory.δ (1 : Fin
      4)).toOrderHom =
      (dgModuleConeLowerTriangle A D f).simplex :=
  (SourcePrecomposition.prepend_face_one _ _).trans (dgModuleCofiberFiberLower_precompose A D f)

/-- 上側比較の零面は標準 fiber の上三角形。 -/
lemma dgModuleCofiberFiberComparisonUpper_face_zero (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonUpper A D f).pullback (SimplexCategory.δ (0 : Fin
      4)).toOrderHom =
      (dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex :=
  SourcePrecomposition.prepend_face_zero _ _

/-- 上側比較の一面は元の cofiber の上三角形。 -/
lemma dgModuleCofiberFiberComparisonUpper_face_one (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonUpper A D f).pullback (SimplexCategory.δ (1 : Fin
      4)).toOrderHom =
      (dgModuleConeUpperTriangle A D f).simplex :=
  (SourcePrecomposition.prepend_face_one _ _).trans (dgModuleCofiberFiberUpper_precompose A D f)

/-- 比較三単体は始域・fiber・cofiber の共通三角形で一致する。 -/
lemma dgModuleCofiberFiberComparison_common (f : M ⟶ N) :
    (dgModuleCofiberFiberComparisonLower A D f).pullback (SimplexCategory.δ (2 : Fin
      4)).toOrderHom =
      (dgModuleCofiberFiberComparisonUpper A D f).pullback (SimplexCategory.δ (2 : Fin
        4)).toOrderHom := by
  have hd :
      (dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom =
      (dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom :=
    (dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).d₁.trans (dgModuleFiberUpperTriangle A
      D (moduleConeInr A D f)).d₁.symm
  calc
    _ = SourcePrecomposition.prepend
        ((dgModuleFiberLowerTriangle A D (moduleConeInr A D f)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        (dgModuleCofiberFiberComparisonCycle A D f) := prepend_triangle_face_two _ _
    _ = SourcePrecomposition.prepend
        ((dgModuleFiberUpperTriangle A D (moduleConeInr A D f)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        (dgModuleCofiberFiberComparisonCycle A D f) :=
      prepend_congr hd (heq_of_eq rfl)
    _ = _ := (prepend_triangle_face_two _ _).symm

end SerrePositivity.InfinityCategories
