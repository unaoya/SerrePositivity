module
public import SerrePositivity.InfinityCategories.Derived.TriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonFaces

/-! # 標準 fiber の押し出し比較三単体

概要：標準 cofiber 錐から元の fiber 四角形への上下の比較三単体を構成する。
方針：明示的比較射を三角形に後合成する内部ホーンを充填する。
規約：既知面と欠けた面の両方を保持する。使われ方：D7 の coslice 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 下側の標準 cofiber 三角形と fiber 三角形を結ぶ三単体。 -/
def fiberCofiberComparisonLower (g : B ⟶ D) (h : C ⟶ D) : Simplex S (Complex S) 3 :=
  complexTriangleAppend (pullbackProjectionB g h)
    (pushoutInclusionB (pullbackProjectionB g h) (pullbackProjectionC g h))
    (pushoutDiagonal (pullbackProjectionB g h) (pullbackProjectionC g h))
    (mappingCone.inl (cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h)))
    (pushoutHomotopy_differential _ _) (fiberCofiberDesc g h)

/-- 上側の標準 cofiber 三角形と fiber 三角形を結ぶ三単体。 -/
def fiberCofiberComparisonUpper (g : B ⟶ D) (h : C ⟶ D) : Simplex S (Complex S) 3 :=
  complexTriangleAppend (pullbackProjectionC g h)
    (pushoutInclusionC (pullbackProjectionB g h) (pullbackProjectionC g h))
    (pushoutDiagonal (pullbackProjectionB g h) (pullbackProjectionC g h)) 0
    (by simp only [δ_zero, pushoutDiagonal, sub_self]) (fiberCofiberDesc g h)

/-- 下側比較の三面は標準 cofiber の下三角形。 -/
lemma fiberCofiberComparisonLower_face_three (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonLower g h).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (cofiberLowerTriangle (pullbackProjectionB g h) (pullbackProjectionC g h)).simplex :=
  complexTriangleAppend_face_three _ _ _ _ _ _

/-- 上側比較の三面は標準 cofiber の上三角形。 -/
lemma fiberCofiberComparisonUpper_face_three (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonUpper g h).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (cofiberUpperTriangle (pullbackProjectionB g h) (pullbackProjectionC g h)).simplex :=
  complexTriangleAppend_face_three _ _ _ _ _ _

/-- 下側比較の二面は元の fiber の下三角形。 -/
lemma fiberCofiberComparisonLower_face_two (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonLower g h).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (fiberLowerTriangle g h).simplex :=
  (complexTriangleAppend_face_two _ _ _ _ _ _).trans (fiberCofiberLower_postcompose g h)

/-- 上側比較の二面は元の fiber の上三角形。 -/
lemma fiberCofiberComparisonUpper_face_two (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonUpper g h).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (fiberUpperTriangle g h).simplex :=
  (complexTriangleAppend_face_two _ _ _ _ _ _).trans (fiberCofiberUpper_postcompose g h)

/-- 比較三単体は始域・cofiber・終域を結ぶ共通面で一致する。 -/
lemma fiberCofiberComparison_common (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonLower g h).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (fiberCofiberComparisonUpper g h).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom :=
  (complexTriangleAppend_face_one _ _ _ _ _ _).trans
    (complexTriangleAppend_face_one _ _ _ _ _ _).symm

end SerrePositivity.InfinityCategories
