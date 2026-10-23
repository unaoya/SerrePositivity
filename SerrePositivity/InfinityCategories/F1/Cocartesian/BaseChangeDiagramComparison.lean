module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeEnrichedComparison

/-!
概要：底変換比較を、底の全対象・全射と全 fibration の全高次 Hom で同時に束ねる。
方針：元の全相対 Hom の作用の可換式と、底上の厳密な自然性を同じ比較へ渡す。
規約：評価後は構成済みの同じ strict transport の自然変換を回収する。
使われ方：同じ分類主写像と底変換後の主写像の大域的な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の底変換比較は、底全体と元の全 fibration の全高次 Hom の両方に関して自然。 -/
def cocartesianBaseChangeDiagramComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) :
    QuasicategoryEnrichedDiagramComparison
      ((cocartesianStrictTransportEnrichedDiagram C).reindex k)
      ((cocartesianStrictTransportEnrichedDiagram D).precompose
        (cocartesianFibrationBaseChangeEnriched (nerveMap k))) where
  app d := cocartesianBaseChangeEnrichedComparison k d
  naturality f p := cocartesianStrictTransportBaseChangeComponent_naturality p.val.hom k f

/-- 元の fibration で評価した同じ比較は、構成済みの元の自然変換を厳密に回収する。 -/
lemma cocartesianBaseChangeDiagramComparison_evaluate
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p : CocartesianFibrationObject (nerve C)) :
    Functor.whiskerRight ((cocartesianBaseChangeDiagramComparison k).evaluate p)
      quasicategoryObjectForget = cocartesianStrictTransportBaseChange p.val.hom k := rfl

end SerrePositivity.InfinityCategories
