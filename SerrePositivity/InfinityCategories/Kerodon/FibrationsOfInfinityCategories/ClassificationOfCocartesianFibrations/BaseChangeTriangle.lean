module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramTriangle
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparisonLaws
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityDiagramComparison

/-!
概要：元の二回の底変換比較と直接の比較を三辺に持つ、底全体の同じ豊穣三角形。
方針：二回目の比較を同じ結合同型で直接の底変換へ戻し、元の厳密な合成則を使う。
規約：全 fibration と全高次 Hom の自然性を保持する。
使われ方：元の比較 span の合成と二次元 Segal 比較の整合性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の底変換比較の合成則を三辺に持つ、底全体・全 Hom の同じ三角形。 -/
def cocartesianBaseChangeTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) (Fin 3 × A) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangle
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k))

/-- 最初の辺は、元の最初の底変換比較の同じ成分。 -/
lemma cocartesianBaseChangeTriangle_first (a : A) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) :
    ((cocartesianBaseChangeTriangle l k).map
      ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))).val p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p.val.hom k (l.obj a) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangle_first ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k)) a p

/-- 次の辺は、元の二回目の比較を同じ結合同型へ合成したもの。 -/
lemma cocartesianBaseChangeTriangle_second (a : A) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) :
    ((cocartesianBaseChangeTriangle l k).map
      ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a))).val p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent (pullback.fst (nerveMap k) p.val.hom) l a ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangle_second ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k)) a p

/-- 長辺は、元の合成した底変換の比較そのものである。 -/
lemma cocartesianBaseChangeTriangle_long (a : A) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) :
    ((cocartesianBaseChangeTriangle l k).map
      ((homOfLE (show (0 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((2 : Fin 3), a))).val p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p.val.hom (l ⋙ k) a := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangle_long ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison k).reindex l)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeDiagramComparison l).precompose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k)) a p
  exact h.trans ((Category.assoc _ _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_comp p.val.hom l k a))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
