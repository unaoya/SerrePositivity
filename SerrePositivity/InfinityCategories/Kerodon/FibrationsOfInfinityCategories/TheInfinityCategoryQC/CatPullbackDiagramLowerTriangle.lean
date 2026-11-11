module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackDiagramUpperTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeDiagramLowerTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeTetrahedronLowerSides

/-!
概要：引き戻し図式の下側の比較三角形と三辺。
方針：全錐の同じ指定円柱を形状の射で制限する。
規約：図式の射と切断の成分を厳密に保持する。
使われ方：三つの比較三単体の合成関係の照合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：同じ指定図式円柱の下側の三角形。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
def catPullbackDiagramLowerTriangle (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDiagramLowerTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge (nerve.edgeMk f).toTruncated)
/-- 概要：最後の辺は切断の終域での指定成分。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma catPullbackDiagramLowerTriangle_zero (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 (catPullbackDiagramLowerTriangle p q f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q).app j)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDiagramLowerTriangle_zero _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy_diagramEdge p q j)
/-- 概要：長辺は同じ共通の対角関手。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma catPullbackDiagramLowerTriangle_one (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 (catPullbackDiagramLowerTriangle p q f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramDiagonal p q f)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDiagramLowerTriangle_one _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramDiagonal_edge p q f).symm
/-- 概要：最初の辺は元の図式の指定射。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma catPullbackDiagramLowerTriangle_two (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 (catPullbackDiagramLowerTriangle p q f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q).map f)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDiagramLowerTriangle_two _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge _ f)
/-- 概要：最後の比較三単体の図式側の面は指定された下側の三角形。
方針：円柱の側面の式を指定図式の辺に適用する。
規約：元の二単体の厳密な等式。
使われ方：四面の合成則へ図式側の指定同型を代入する。 -/
lemma catPullbackDiagramLowerTriangle_tetrahedron (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTetrahedron p q f 2) =
      catPullbackDiagramLowerTriangle p q f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTetrahedron_lower_last p q f).trans (by rfl)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
