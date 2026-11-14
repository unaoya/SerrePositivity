module
public import SerrePositivity.HomologicalAlgebra.ProductTotalFirstRow
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardZeroLeg
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：次数零の標準脚に二つの余面を合成した鎖写像の指定ホモトピー。
方針：横微分を交代余面の差と同定し、第一行の同じ射影の零ホモトピーを移す。
規約：対象ごとのホモトピーの存在だけで済ませず、元の積全複体の射影を使う。
使われ方：HA 1.2.4、G10 の標準脚の高次の両立への最初の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive AlgebraicTopology
open SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

/-- 零行から第一行への横微分は、同じ二つの余面の差。 -/
theorem firstRowDifferential (X : CosimplicialObject (Complex A)) :
    ((doubleComplexFunctor A).obj X).d 0 1 ≫ (rowIso X 1).hom =
      (rowIso X 0).hom ≫ (X.δ 0 - X.δ 1) := by
  have hd : ((alternatingCofaceMapComplex (Complex A)).obj X).d 0 1 = X.δ 0 - X.δ 1 := by
    change CochainComplex.of.d (fun n => X.obj ⦋n⦌) (AlternatingCofaceMapComplex.objD X) 0 (0+1) = _
    rw [CochainComplex.of_d]
    simp [AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]
  change (((alternatingCofaceMapComplex (Complex A)).obj X).extend
    ComplexShape.embeddingUpNat).d 0 1 ≫ _ = _
  rw [HomologicalComplex.extend_d_eq ((alternatingCofaceMapComplex (Complex A)).obj X)
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl (j := 1) (j' := (1 : ℤ)) rfl]
  rw [hd]
  simp [rowIso]

/-- 二つの余面の前の標準脚は、同じ第一行の射影でホモトピック。 -/
def standardCofaceHomotopy (X : CosimplicialObject (Complex A)) :
    Homotopy (standardZeroLeg A X ≫ X.δ 0) (standardZeroLeg A X ≫ X.δ 1) := by
  refine Homotopy.equivSubZero.symm ?_
  have h := (SerrePositivity.HomologicalAlgebra.ProductTotal.firstRowHomotopy
    ((doubleComplexFunctor A).obj X) (negativeToZeroRow_d A X)).compRight (rowIso X 1).hom
  have he : (SerrePositivity.HomologicalAlgebra.ProductTotal.zeroRowHom
      ((doubleComplexFunctor A).obj X) (negativeToZeroRow_d A X) ≫
        ((doubleComplexFunctor A).obj X).d 0 1) ≫ (rowIso X 1).hom =
      standardZeroLeg A X ≫ X.δ 0 - standardZeroLeg A X ≫ X.δ 1 := by
    rw [Category.assoc, firstRowDifferential]
    simp [standardZeroLeg, Category.assoc, comp_sub]
  simpa only [he, zero_comp] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
