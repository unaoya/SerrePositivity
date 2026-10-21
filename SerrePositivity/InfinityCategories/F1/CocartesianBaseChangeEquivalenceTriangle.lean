module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleInvertible
public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleFamily

/-!
概要：元の底変換比較三角形の全パラメーターを可逆三角形の空間へ持ち上げる。
方針：元の同じ大域二単体の三辺の可逆性を、各 fibration で評価する。
規約：包含後は元の三角形族、長辺は既存の直接の区間族そのもの。
使われ方：元の Hom 比較 span の合成を同じ三角形で比較する。
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

/-- 同じ元の大域二単体の三辺は全て可逆。 -/
lemma cocartesianBaseChangeGlobalTriangleSimplex_isInvertible (i : Fin 3) :
    IsInvertibleEdge (edgeOfSimplex
      (((ihom (CocartesianFibrationInfinity (nerve C))).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ i
          (cocartesianBaseChangeGlobalTriangleSimplex l k))) := by
  fin_cases i
  · exact cocartesianBaseChangeGlobalTriangleSimplex_second_isInvertible l k
  · exact cocartesianBaseChangeGlobalTriangleSimplex_long_isInvertible l k
  · exact cocartesianBaseChangeGlobalTriangleSimplex_first_isInvertible l k

/-- 元の全 fibration 上の同じ比較三角形を可逆三角形の空間へ持ち上げる。 -/
def cocartesianBaseChangeEquivalenceTriangle :
    CocartesianFibrationInfinity (nerve C) ⟶
      equivalenceTriangle (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  equivalenceTriangleFamilyLift (cocartesianBaseChangeTriangleCurryFamily l k)
    (cocartesianBaseChangeGlobalTriangleSimplex_isInvertible l k)

/-- 同じ持ち上げは、包含後に元の全高次の三角形族を回収する。 -/
lemma cocartesianBaseChangeEquivalenceTriangle_ι :
    cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleι _ =
      cocartesianBaseChangeTriangleCurryFamily l k :=
  equivalenceTriangleFamilyLift_ι _ _

/-- 同じ持ち上げの長辺は、包含後に既存の直接の比較の元の区間族を回収する。 -/
lemma cocartesianBaseChangeEquivalenceTriangle_long_ι :
    cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 1 ≫
      equivalencePathι _ = cocartesianBaseChangeJointIntervalFamily (l ⋙ k) := by
  rw [cocartesianBaseChangeEquivalenceTriangle, equivalenceTriangleFamilyLift_face_ι,
    cocartesianBaseChangeTriangleCurryFamily_long]

end SerrePositivity.InfinityCategories
