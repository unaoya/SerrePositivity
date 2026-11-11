module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeTriangleFirstRestriction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonIndexTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeComparisonYoneda

/-!
概要：同じ底変換三角形を元の全 fibration 上の関手空間の二単体にする。
方針：同じ二変数の族を転置し、面の制限を既存の元の比較辺へ戻す。
規約：最初の辺と長辺は既存の比較辺そのもの。
使われ方：元の Hom 比較 span の合成を同じ三角形で接続する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ族の転置は、元の値域への後合成と厳密に可換。 -/
lemma transposeFunctorFamily_post {A I X Y : SSet.{u}} (F : A ⟶ (ihom I).obj X) (g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (F ≫ (ihom I).map g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F ≫ (ihom A).map g := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily, uncurry_curry, uncurry_natural_right,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily, uncurry_natural_right, uncurry_curry, Category.assoc]

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の全 fibration 上の関手空間内で、同じ比較三辺を持つ三角形。 -/
def cocartesianBaseChangeTriangleMap :
    (Δ[2] : SSet.{u + 1}) ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeTriangleCurryFamily l k)

/-- 同じ三角形の長辺の族は、既存の直接の比較辺を与える元の転置族。 -/
lemma cocartesianBaseChangeTriangleMap_long :
    stdSimplex.δ (1 : Fin 3) ≫ cocartesianBaseChangeTriangleMap l k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointIntervalFamily (l ⋙ k)) := by
  rw [cocartesianBaseChangeTriangleMap, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.transposeFunctorFamily_pre,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeTriangleCurryFamily_long]

/-- 同じ三角形の最初の辺の族は、既存の比較辺の元の底制限。 -/
lemma cocartesianBaseChangeTriangleMap_first :
    stdSimplex.δ (2 : Fin 3) ≫ cocartesianBaseChangeTriangleMap l k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointIntervalFamily k) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).map
          ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}) := by
  rw [cocartesianBaseChangeTriangleMap, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.transposeFunctorFamily_pre,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeTriangleCurryFamily_first_restriction, transposeFunctorFamily_post]

/-- 元の全 fibration 上の同じ関手空間内の、実際の二単体。 -/
def cocartesianBaseChangeGlobalTriangleSimplex :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) _⦋2⦌ :=
  SSet.yonedaEquiv (cocartesianBaseChangeTriangleMap l k)

/-- 同じ大域二単体の長辺は、既存の元の直接の底変換比較辺そのもの。 -/
lemma cocartesianBaseChangeGlobalTriangleSimplex_long :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (1 : Fin 3)
        (cocartesianBaseChangeGlobalTriangleSimplex l k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge (l ⋙ k)).edge := by
  rw [cocartesianBaseChangeGlobalTriangleSimplex, ← stdSimplex.yonedaEquiv_δ_comp,
    cocartesianBaseChangeTriangleMap_long]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge_yoneda (l ⋙ k)

/-- 同じ大域二単体の最初の辺は、既存の元の比較辺を底で制限した辺そのもの。 -/
lemma cocartesianBaseChangeGlobalTriangleSimplex_first :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (2 : Fin 3)
        (cocartesianBaseChangeGlobalTriangleSimplex l k) =
      ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).map
        ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u})).app
          (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge k).edge := by
  rw [cocartesianBaseChangeGlobalTriangleSimplex, ← stdSimplex.yonedaEquiv_δ_comp,
    cocartesianBaseChangeTriangleMap_first, SSet.yonedaEquiv_comp]
  exact congrArg (fun e ↦
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).map
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u})).app
        (Opposite.op ⦋1⦌) e) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge_yoneda k)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
