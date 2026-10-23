module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramTriangle
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramComparisonLaws
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityDiagramComparison

/-!
概要：元の二回の底変換比較と直接の比較を三辺に持つ、底全体の同じ豊穣三角形。
方針：二回目の比較を同じ結合同型で直接の底変換へ戻し、元の厳密な合成則を使う。
規約：全 fibration と全高次 Hom の自然性を保持する。
使われ方：元の比較 span の合成と二次元 Segal 比較の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の底変換比較の合成則を三辺に持つ、底全体・全 Hom の同じ三角形。 -/
def cocartesianBaseChangeTriangle :
    QuasicategoryEnrichedDiagram (CocartesianFibrationObject (nerve C)) (Fin 3 × A) :=
  quasicategoryEnrichedDiagramTriangle
    ((cocartesianBaseChangeDiagramComparison k).reindex l)
    (((cocartesianBaseChangeDiagramComparison l).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (cocartesianBaseChangeAssociativityDiagramComparison l k))

/-- 最初の辺は、元の最初の底変換比較の同じ成分。 -/
lemma cocartesianBaseChangeTriangle_first (a : A) (p : CocartesianFibrationObject (nerve C)) :
    ((cocartesianBaseChangeTriangle l k).map
      ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))).val p =
      cocartesianStrictTransportBaseChangeComponent p.val.hom k (l.obj a) := by
  exact quasicategoryEnrichedDiagramTriangle_first ((cocartesianBaseChangeDiagramComparison k).reindex l)
    (((cocartesianBaseChangeDiagramComparison l).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (cocartesianBaseChangeAssociativityDiagramComparison l k)) a p

/-- 次の辺は、元の二回目の比較を同じ結合同型へ合成したもの。 -/
lemma cocartesianBaseChangeTriangle_second (a : A) (p : CocartesianFibrationObject (nerve C)) :
    ((cocartesianBaseChangeTriangle l k).map
      ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a))).val p =
      cocartesianStrictTransportBaseChangeComponent (pullback.fst (nerveMap k) p.val.hom) l a ≫
        (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := by
  exact quasicategoryEnrichedDiagramTriangle_second ((cocartesianBaseChangeDiagramComparison k).reindex l)
    (((cocartesianBaseChangeDiagramComparison l).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (cocartesianBaseChangeAssociativityDiagramComparison l k)) a p

/-- 長辺は、元の合成した底変換の比較そのものである。 -/
lemma cocartesianBaseChangeTriangle_long (a : A) (p : CocartesianFibrationObject (nerve C)) :
    ((cocartesianBaseChangeTriangle l k).map
      ((homOfLE (show (0 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((2 : Fin 3), a))).val p =
      cocartesianStrictTransportBaseChangeComponent p.val.hom (l ⋙ k) a := by
  have h := quasicategoryEnrichedDiagramTriangle_long ((cocartesianBaseChangeDiagramComparison k).reindex l)
    (((cocartesianBaseChangeDiagramComparison l).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
        (cocartesianBaseChangeAssociativityDiagramComparison l k)) a p
  exact h.trans ((Category.assoc _ _ _).symm.trans
    (cocartesianStrictTransportBaseChangeComponent_comp p.val.hom l k a))

end SerrePositivity.InfinityCategories
