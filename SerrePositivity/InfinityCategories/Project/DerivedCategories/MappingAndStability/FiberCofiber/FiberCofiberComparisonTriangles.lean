module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberCofiberComparisonFaces

/-! # 標準 fiber の押し出し比較三単体

概要：標準 cofiber 錐から元の fiber 四角形への上下の比較三単体を構成する。
方針：明示的比較射を三角形に後合成する内部ホーンを充填する。
規約：既知面と欠けた面の両方を保持する。使われ方：D7 の coslice 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 下側の標準 cofiber 三角形と fiber 三角形を結ぶ三単体。 -/
def fiberCofiberComparisonLower (g : B ⟶ D) (h : C ⟶ D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutHomotopy_differential _ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h)

/-- 上側の標準 cofiber 三角形と fiber 三角形を結ぶ三単体。 -/
def fiberCofiberComparisonUpper (g : B ⟶ D) (h : C ⟶ D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) 0
    (by simp only [δ_zero, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal, sub_self]) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h)

/-- 下側比較の三面は標準 cofiber の下三角形。 -/
lemma fiberCofiberComparisonLower_face_three (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonLower g h).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberLowerTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_three _ _ _ _ _ _

/-- 上側比較の三面は標準 cofiber の上三角形。 -/
lemma fiberCofiberComparisonUpper_face_three (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonUpper g h).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberUpperTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_three _ _ _ _ _ _

/-- 下側比較の二面は元の fiber の下三角形。 -/
lemma fiberCofiberComparisonLower_face_two (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonLower g h).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_two _ _ _ _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberLower_postcompose g h)

/-- 上側比較の二面は元の fiber の上三角形。 -/
lemma fiberCofiberComparisonUpper_face_two (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonUpper g h).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_two _ _ _ _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberUpper_postcompose g h)

/-- 比較三単体は始域・cofiber・終域を結ぶ共通面で一致する。 -/
lemma fiberCofiberComparison_common (g : B ⟶ D) (h : C ⟶ D) :
    (fiberCofiberComparisonLower g h).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (fiberCofiberComparisonUpper g h).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_one _ _ _ _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_one _ _ _ _ _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
