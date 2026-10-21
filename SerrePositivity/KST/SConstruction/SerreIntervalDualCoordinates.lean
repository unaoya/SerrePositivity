module
public import SerrePositivity.KST.SConstruction.SerreIntervalTensorExt

/-! # 元の鎖区間の直和表示による双対座標
概要：元の区間の単位成分・境界成分・辺成分を、元の直和射影で取り出す。
方針：元の単位・disk の次数同型と元の biprod 射影を使う。
規約：元の区間・端点・辺を保持。使われ方：任意の生成元値から次数線形射を復元する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の区間の零次数の単位直和成分を取る座標。 -/
def serreIntervalUnitCoordinate : (serreInterval A).X 0 ⟶ 𝟙_ (ModuleCat A) :=
  (biprod.fst : serreInterval A ⟶ 𝟙_ (Complex A)).f 0 ≫
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom

/-- 元の区間の零次数の disk 上側成分を取る座標。 -/
def serreIntervalBoundaryCoordinate : (serreInterval A).X 0 ⟶ 𝟙_ (ModuleCat A) :=
  (biprod.snd : serreInterval A ⟶ complexDisk A (-1)).f 0 ≫ (complexDiskX₁ A (-1)).hom

/-- 元の区間の次数 −1 の disk 下側成分を取る座標。 -/
def serreIntervalEdgeCoordinate : (serreInterval A).X (-1) ⟶ 𝟙_ (ModuleCat A) :=
  (biprod.snd : serreInterval A ⟶ complexDisk A (-1)).f (-1) ≫ (complexDiskX₀ A (-1)).hom

/-- 元の零端点の単位成分は一。 -/
lemma serreIntervalUnitCoordinate_zero :
    serreIntervalUnitCoordinate A (cycleFromUnit _ (serreIntervalZero A)).val = 1 := by
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    (((biprod.inl ≫ biprod.fst : 𝟙_ (Complex A) ⟶ 𝟙_ (Complex A)).f 0)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1)) = 1
  rw [biprod.inl_fst]
  exact ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv_hom_id 1

/-- 元の零端点の境界成分は零。 -/
lemma serreIntervalBoundaryCoordinate_zero :
    serreIntervalBoundaryCoordinate A (cycleFromUnit _ (serreIntervalZero A)).val = 0 := by
  change (complexDiskX₁ A (-1)).hom
    (((biprod.inl ≫ biprod.snd : 𝟙_ (Complex A) ⟶ complexDisk A (-1)).f 0)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1)) = 0
  rw [biprod.inl_snd]
  exact map_zero _

/-- 元の disk 上側生成元の区間内の像は、単位成分零。 -/
lemma serreIntervalUnitCoordinate_upper :
    serreIntervalUnitCoordinate A
        ((biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f 0
          ((complexDiskX₁ A (-1)).inv 1)) = 0 := by
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    (((biprod.inr ≫ biprod.fst : complexDisk A (-1) ⟶ 𝟙_ (Complex A)).f 0)
      ((complexDiskX₁ A (-1)).inv 1)) = 0
  rw [biprod.inr_fst]
  exact map_zero _

/-- 元の disk 上側生成元の区間内の像は、境界成分一。 -/
lemma serreIntervalBoundaryCoordinate_upper :
    serreIntervalBoundaryCoordinate A
        ((biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f 0
          ((complexDiskX₁ A (-1)).inv 1)) = 1 := by
  change (complexDiskX₁ A (-1)).hom
    (((biprod.inr ≫ biprod.snd : complexDisk A (-1) ⟶ complexDisk A (-1)).f 0)
      ((complexDiskX₁ A (-1)).inv 1)) = 1
  rw [biprod.inr_snd]
  exact ConcreteCategory.congr_hom (complexDiskX₁ A (-1)).inv_hom_id 1

/-- 元の辺生成元の辺成分は一。 -/
lemma serreIntervalEdgeCoordinate_edge :
    serreIntervalEdgeCoordinate A (serreIntervalEdge A) = 1 := by
  change (complexDiskX₀ A (-1)).hom
    (((biprod.inr ≫ biprod.snd : complexDisk A (-1) ⟶ complexDisk A (-1)).f (-1))
      ((complexDiskX₀ A (-1)).inv 1)) = 1
  rw [biprod.inr_snd]
  exact ConcreteCategory.congr_hom (complexDiskX₀ A (-1)).inv_hom_id 1

end SerrePositivity.KST.SConstruction
