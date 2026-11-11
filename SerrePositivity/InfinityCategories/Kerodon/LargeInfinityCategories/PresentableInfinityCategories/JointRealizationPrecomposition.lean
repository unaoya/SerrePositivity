module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CurryPrecomposition

/-!
概要：共同比較を豊穣前合成してから実現する指定同型を、元の実現同型の前合成へ同定する。
方針：共同族の前合成、curry の自然性、元の端点等式の移送を順に比較する。
規約：元の realizationIso と元の豊穣関手を保持する。
使われ方：P-12 の反復底変換の合成式を指定された降下同型へ接続する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：前合成した比較の指定実現同型は、元の指定実現同型の関手前合成。
方針：共同辺の像を curry し、前後二通りの端点移送を正規化する。
規約：全図式の同型の等式で、各成分での存在へ弱めない。
使われ方：二段の相対切断底変換の実現から指定 straightening 比較への降下。 -/
lemma jointRealizationIso_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose η H).realizationIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose_isQCatEquivalence η H hη) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (D.realization_precompose H).symm (E.realization_precompose H).symm
        ((η.realizationIso hη).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointRealizationIso_normalized, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonIso_precompose η H hη,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_comp]
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H
  let e := η.jointComparisonIso hη
  let hf := curry_natural_left q D.jointEvaluation
  let hg := curry_natural_left q E.jointEvaluation
  let hd := (congrArg curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointEvaluation_precompose D H).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointEvaluation_curry (D.precompose H))
  let he := (congrArg curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointEvaluation_precompose E H).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointEvaluation_curry (E.precompose H))
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (hf.symm.trans hd) (hg.symm.trans he)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr hf hg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry
          (e.precomp (((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ◁ q)))) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_comp hf hg (hf.symm.trans hd) (hg.symm.trans he)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (e.precomp
          (((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ◁ q)))).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (hf.symm.trans hd) (hg.symm.trans he) (e.curry.precomp q) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoCurry_precompose_second]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointRealizationIso_normalized η hη, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
