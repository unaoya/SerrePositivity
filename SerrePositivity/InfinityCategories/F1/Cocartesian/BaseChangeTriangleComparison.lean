module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangle
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramComparisonExt

/-!
概要：元の豊穣三角形の合成比較は、既存の元の直接の底変換比較そのもの。
方針：同じ全対象の成分の厳密な合成則を、元の図式比較の等式へ束ねる。
規約：元の底全体と全高次 Hom の比較を保持する。
使われ方：三角形の長辺を既存の比較 span へ厳密に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 三角形の元の合成比較は、元の直接の比較と図式全体で厳密に等しい。 -/
lemma cocartesianBaseChangeTriangle_comparison
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    ((cocartesianBaseChangeDiagramComparison k).reindex l).trans
      (((cocartesianBaseChangeDiagramComparison l).precompose
        (cocartesianFibrationBaseChangeEnriched (nerveMap k))).trans
          (cocartesianBaseChangeAssociativityDiagramComparison l k)) =
      cocartesianBaseChangeDiagramComparison (l ⋙ k) := by
  apply QuasicategoryEnrichedDiagramComparison.extPointwise
  intro a p
  change cocartesianStrictTransportBaseChangeComponent p.val.hom k (l.obj a) ≫
      (cocartesianStrictTransportBaseChangeComponent (pullback.fst (nerveMap k) p.val.hom) l a ≫
        (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom) =
    cocartesianStrictTransportBaseChangeComponent p.val.hom (l ⋙ k) a
  exact (Category.assoc _ _ _).symm.trans
    (cocartesianStrictTransportBaseChangeComponent_comp p.val.hom l k a)

end SerrePositivity.InfinityCategories
