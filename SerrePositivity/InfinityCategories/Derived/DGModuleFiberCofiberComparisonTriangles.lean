module
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberSquare
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 標準 cone の左包含が満たす合成三角形の微分式。 -/
lemma dgModuleConeTriangle_differential (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
      (moduleConeInlElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ moduleConeInr A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (0 : M ⟶ moduleCone A D f))).val := by
  rw [moduleHomCycle_zero, sub_zero]
  exact moduleConeInlElement_d A D f

/-- 下側の標準 cone 三角形と fiber 三角形を結ぶ実三単体。 -/
def dgModuleFiberCofiberComparisonLower (f : M ⟶ N) : Simplex A (RightModule A D) 3 :=
  dgModuleTriangleAppend A D (dgModuleFiberProjection A D f)
    (moduleConeInr A D (dgModuleFiberProjection A D f)) 0
    (moduleConeInlElement A D (dgModuleFiberProjection A D f))
    (dgModuleConeTriangle_differential A D _) (dgModuleFiberCofiberDesc A D f)

/-- 上側の零三角形を結ぶ実三単体。 -/
def dgModuleFiberCofiberComparisonUpper (f : M ⟶ N) : Simplex A (RightModule A D) 3 :=
  dgModuleTriangleAppend A D
    (0 : ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶ moduleZero A D)
    (0 : moduleZero A D ⟶ moduleCone A D (dgModuleFiberProjection A D f)) 0 0
    (by rw [zero_comp, sub_self]; exact map_zero _) (dgModuleFiberCofiberDesc A D f)

/-- 下側比較の三面は標準 cone の下三角形。 -/
lemma dgModuleFiberCofiberComparisonLower_face_three (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (dgModuleConeLowerTriangle A D (dgModuleFiberProjection A D f)).simplex :=
  dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

/-- 上側比較の三面は標準 cone の上三角形。 -/
lemma dgModuleFiberCofiberComparisonUpper_face_three (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (dgModuleConeUpperTriangle A D (dgModuleFiberProjection A D f)).simplex :=
  dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

/-- 比較三単体の一面は共通の対角と降下射の厳密三角形。 -/
lemma dgModuleFiberCofiberComparison_common (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (dgModuleFiberCofiberComparisonUpper A D f).pullback
        (SimplexCategory.δ (1 : Fin 4)).toOrderHom :=
  (dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).trans
    (dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).symm

/-- 下側比較の欠けた面は元の fiber の下三角形。 -/
lemma dgModuleFiberCofiberComparisonLower_face_two (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (dgModuleFiberLowerTriangle A D f).simplex := by
  unfold dgModuleFiberCofiberComparisonLower
  rw [dgModuleTriangleAppend_face_two]
  unfold postcomposeDGModuleTriangle
  apply dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [dgModuleCompStruct_obj, dgModuleFiberLowerTriangle,
        HomotopyComparison.tripleObj]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_edge01, dgModuleFiberLowerTriangle]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_edge12, dgModuleFiberLowerTriangle,
      dgModuleFiberCofiberDesc_inr]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_edge02, dgModuleFiberLowerTriangle, zero_comp]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_triple, dgModuleFiberLowerTriangle]
    exact dgModuleFiberCofiberDesc_inl A D f

/-- 上側比較の欠けた面は元の fiber の上三角形。 -/
lemma dgModuleFiberCofiberComparisonUpper_face_two (f : M ⟶ N) :
    (dgModuleFiberCofiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (dgModuleFiberUpperTriangle A D f).simplex := by
  unfold dgModuleFiberCofiberComparisonUpper
  rw [dgModuleTriangleAppend_face_two]
  unfold postcomposeDGModuleTriangle
  apply dgSimplex2_ext
  · funext i
    fin_cases i <;>
      simp only [dgModuleCompStruct_obj, dgModuleFiberUpperTriangle,
        HomotopyComparison.tripleObj]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_edge01, dgModuleFiberUpperTriangle]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_edge12, dgModuleFiberUpperTriangle, zero_comp]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_edge02, dgModuleFiberUpperTriangle, zero_comp]
  · apply heq_of_eq
    simp only [dgModuleCompStruct_triple, dgModuleFiberUpperTriangle]
    exact compose_zero _ _

end SerrePositivity.InfinityCategories
