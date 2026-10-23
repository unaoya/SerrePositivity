module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeEquivalenceTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomPath
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleFunctorEdgePathEdgeFamily
public import SerrePositivity.InfinityCategories.Core.EquivalencePathMap

/-!
概要：同じ可逆三角形の面は、既存の元の Hom 比較 path そのもの。
方針：全部分複体への包含の単射性と元の区間族の厳密な面の公式を使う。
規約：比較の代表も全高次のパラメーターも変更しない。
使われ方：元の Hom 比較 span の合成則を同じ三角形で取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 既存の元の Hom 比較 path は、包含後に元の同じ区間族を回収する。 -/
lemma cocartesianBaseChangeHomPath_ι
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) :
    cocartesianBaseChangeHomPath k ≫ equivalencePathι _ =
      cocartesianBaseChangeJointIntervalFamily k :=
  invertibleFunctorEdgePath_ι_of_edge_family
    (A := CocartesianFibrationInfinity (nerve C))
    (Y := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve D)))
    (cocartesianBaseChangeJointComparisonEdge k)
    (cocartesianBaseChangeJointComparisonEdge_isInvertible k)
    (cocartesianBaseChangeJointIntervalFamily k)
    (cocartesianBaseChangeJointComparisonEdge_yoneda k)

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ可逆三角形の長辺は、既存の元の直接の Hom 比較 path そのもの。 -/
lemma cocartesianBaseChangeEquivalenceTriangle_long :
    cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 1 =
      cocartesianBaseChangeHomPath (l ⋙ k) := by
  have : Mono (equivalencePathι
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
  apply (cancel_mono (equivalencePathι _)).mp
  rw [Category.assoc, cocartesianBaseChangeEquivalenceTriangle_long_ι,
    cocartesianBaseChangeHomPath_ι]

/-- 同じ可逆三角形の最初の辺は、既存の元の Hom 比較 path の同じ底制限。 -/
lemma cocartesianBaseChangeEquivalenceTriangle_first :
    cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 2 =
      cocartesianBaseChangeHomPath k ≫ equivalencePathMap
        ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u}) := by
  have : Mono (equivalencePathι
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
  apply (cancel_mono (equivalencePathι _)).mp
  rw [Category.assoc, cocartesianBaseChangeEquivalenceTriangle,
    equivalenceTriangleFamilyLift_face_ι,
    cocartesianBaseChangeTriangleCurryFamily_first_restriction,
    Category.assoc]
  change cocartesianBaseChangeJointIntervalFamily k ≫ _ =
    cocartesianBaseChangeHomPath k ≫ equivalencePathMap
      (X := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve D)))
      (Y := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u}) ≫
        equivalencePathι _
  rw [equivalencePathMap_ι, ← Category.assoc, cocartesianBaseChangeHomPath_ι]

end SerrePositivity.InfinityCategories
