module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.JointComparisonReindex
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.CurryFirstPrecomposition

/-!
概要：共同比較を添字関手で制限した指定実現同型を、元の実現同型の値域制限へ同定する。
方針：共同辺の第一変数制限と curry の自然性を、元の端点移送で正規化する。
規約：元の realizationIso と元の添字関手を保持する。
使われ方：P-12 の単体添字制限と指定 straightening 底変換の合成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：添字制限した比較の指定実現同型は、元の指定同型の値域側の制限。
方針：共同辺の像を curry し、前後二通りの端点移送を正規化する。
規約：全図式の同型の等式。使われ方：元の単体添字の底変換比較の合成。 -/
lemma jointRealizationIso_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    (jointComparisonReindex η k).realizationIso
      (jointComparisonReindex_isQCatEquivalence η k hη) =
      diagramIsoCongr (D.realization_reindex k) (E.realization_reindex k)
        ((η.realizationIso hη).postcomp
          ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app SpaceInfinity.{u})) := by
  rw [jointRealizationIso_normalized, jointComparisonIso_reindex η k hη,
    diagramIsoCongr_curry, diagramIsoCongr_comp]
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)
  let e := η.jointComparisonIso hη
  let hf := (curry_pre_app q D.jointEvaluation).symm
  let hg := (curry_pre_app q E.jointEvaluation).symm
  let hd := (congrArg curry (jointEvaluation_reindex D k).symm).trans
    (jointEvaluation_curry (D.reindex k))
  let he := (congrArg curry (jointEvaluation_reindex E k).symm).trans
    (jointEvaluation_curry (E.reindex k))
  calc
    _ = diagramIsoCongr (hf.symm.trans hd) (hg.symm.trans he)
        (diagramIsoCongr hf hg (FunctorIso.curry (e.precomp (q ▷ SimplicialNerve C)))) :=
      (diagramIsoCongr_comp hf hg (hf.symm.trans hd) (hg.symm.trans he)
        (FunctorIso.curry (e.precomp (q ▷ SimplicialNerve C)))).symm
    _ = diagramIsoCongr (hf.symm.trans hd) (hg.symm.trans he)
        (e.curry.postcomp ((pre q).app SpaceInfinity.{u})) := by
      rw [functorIsoCurry_precompose_first]
    _ = _ := by
      rw [jointRealizationIso_normalized η hη, diagramIsoCongr_postcomp, diagramIsoCongr_comp]

end SerrePositivity.InfinityCategories.F2.Presentable
