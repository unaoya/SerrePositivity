module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondTriangleTranspose
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityIso
public import SerrePositivity.InfinityCategories.F1.InvertibleTriangleComposition
public import SerrePositivity.InfinityCategories.F1.InvertibleMappedSimplex

/-!
概要：元の第二比較の分解大域二単体の三辺は全て可逆。
方針：既存の二回目の比較と既存の結合比較の同じ可逆辺を使う。
規約：同じ分解二単体と元の全高次の族を保持する。
使われ方：元の Hom 輸送の第二辺の合成則。
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

/-- 同じ分解二単体の最初の辺は、既存の二回目の比較の前合成として可逆。 -/
lemma cocartesianBaseChangeSecondGlobalTriangleSimplex_first_isInvertible :
    IsInvertibleEdge (edgeOfSimplex
      (((ihom (CocartesianFibrationInfinity (nerve C))).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (2 : Fin 3)
          (cocartesianBaseChangeSecondGlobalTriangleSimplex l k))) := by
  rw [cocartesianBaseChangeSecondGlobalTriangleSimplex_first]
  exact isInvertibleEdge_edgeOfSimplex_map
    (X := (ihom (CocartesianFibrationInfinity (nerve D))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (Y := (ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    ((pre (cocartesianFibrationInfinityBaseChange (nerveMap k))).app
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (cocartesianBaseChangeJointComparisonEdge l)
    (cocartesianBaseChangeJointComparisonEdge_isInvertible l)

/-- 同じ分解二単体の次の辺は、既存の元の結合比較辺として可逆。 -/
lemma cocartesianBaseChangeSecondGlobalTriangleSimplex_second_isInvertible :
    IsInvertibleEdge (edgeOfSimplex
      (((ihom (CocartesianFibrationInfinity (nerve C))).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (0 : Fin 3)
          (cocartesianBaseChangeSecondGlobalTriangleSimplex l k))) := by
  rw [cocartesianBaseChangeSecondGlobalTriangleSimplex_second]
  exact isInvertibleEdge_edgeOfSimplex
    (X := (ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (cocartesianBaseChangeAssociativityEdge l k)
    (cocartesianBaseChangeAssociativityEdge_isInvertible l k)

/-- 同じ分解二単体の三辺は全て可逆。 -/
lemma cocartesianBaseChangeSecondGlobalTriangleSimplex_isInvertible (i : Fin 3) :
    IsInvertibleEdge (edgeOfSimplex
      (((ihom (CocartesianFibrationInfinity (nerve C))).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ i
          (cocartesianBaseChangeSecondGlobalTriangleSimplex l k))) := by
  fin_cases i
  · exact cocartesianBaseChangeSecondGlobalTriangleSimplex_second_isInvertible l k
  · exact isInvertibleEdge_triangle_long_of_first_second _
      (cocartesianBaseChangeSecondGlobalTriangleSimplex_first_isInvertible l k)
      (cocartesianBaseChangeSecondGlobalTriangleSimplex_second_isInvertible l k)
  · exact cocartesianBaseChangeSecondGlobalTriangleSimplex_first_isInvertible l k

end SerrePositivity.InfinityCategories
