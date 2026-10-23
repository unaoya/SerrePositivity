module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondTriangleInvertible
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomPath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTrianglePathFaces

/-!
概要：元の第二比較の分解を、元の可逆三角形の空間へ全パラメーターで持ち上げる。
方針：同じ大域二単体の可逆性と、包含の単射性で元の三つの path を回収する。
規約：長辺は元の比較三角形の第二面そのもの。
使われ方：元の Hom 輸送の第二辺を二回目の比較と結合比較へ分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の第二比較を分解する全 fibration 上の同じ可逆三角形。 -/
def cocartesianBaseChangeSecondEquivalenceTriangle :
    CocartesianFibrationInfinity (nerve C) ⟶
      equivalenceTriangle (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  equivalenceTriangleFamilyLift (cocartesianBaseChangeSecondTriangleCurryFamily l k)
    (cocartesianBaseChangeSecondGlobalTriangleSimplex_isInvertible l k)

/-- 同じ分解三角形の包含は、元の全高次の二単体族を回収する。 -/
lemma cocartesianBaseChangeSecondEquivalenceTriangle_ι :
    cocartesianBaseChangeSecondEquivalenceTriangle l k ≫ equivalenceTriangleι _ =
      cocartesianBaseChangeSecondTriangleCurryFamily l k :=
  equivalenceTriangleFamilyLift_ι _ _

/-- 同じ分解三角形の最初の面は、既存の二回目の比較 path の元の前合成。 -/
lemma cocartesianBaseChangeSecondEquivalenceTriangle_first :
    cocartesianBaseChangeSecondEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 2 =
      cocartesianFibrationInfinityBaseChange (nerveMap k) ≫ cocartesianBaseChangeHomPath l := by
  have : Mono (equivalencePathι
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
  apply (cancel_mono (equivalencePathι _)).mp
  rw [Category.assoc, cocartesianBaseChangeSecondEquivalenceTriangle,
    equivalenceTriangleFamilyLift_face_ι, cocartesianBaseChangeSecondTriangleCurryFamily_first,
    Category.assoc, cocartesianBaseChangeHomPath_ι]

/-- 同じ分解三角形の次の面は、既存の元の結合比較 path そのもの。 -/
lemma cocartesianBaseChangeSecondEquivalenceTriangle_second :
    cocartesianBaseChangeSecondEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0 =
      cocartesianBaseChangeAssociativityHomPath l k := by
  have : Mono (equivalencePathι
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
  apply (cancel_mono (equivalencePathι _)).mp
  rw [Category.assoc, cocartesianBaseChangeSecondEquivalenceTriangle,
    equivalenceTriangleFamilyLift_face_ι, cocartesianBaseChangeSecondTriangleCurryFamily_second,
    cocartesianBaseChangeAssociativityHomPath_ι]

/-- 同じ分解三角形の長辺は、元の比較三角形の第二面の同じ path そのもの。 -/
lemma cocartesianBaseChangeSecondEquivalenceTriangle_long :
    cocartesianBaseChangeSecondEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 1 =
      cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0 := by
  have : Mono (equivalencePathι
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
  apply (cancel_mono (equivalencePathι _)).mp
  simp only [Category.assoc]
  rw [cocartesianBaseChangeSecondEquivalenceTriangle, equivalenceTriangleFamilyLift_face_ι,
    cocartesianBaseChangeEquivalenceTriangle, equivalenceTriangleFamilyLift_face_ι,
    cocartesianBaseChangeSecondTriangleCurryFamily_long]

end SerrePositivity.InfinityCategories
