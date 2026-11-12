module

public import SerrePositivity.KST.NonConnective.SequentialHomStep

/-!
概要：段ごとの普遍 Hom 族は、元のスペクトルの構造射と厳密に整合する。
方針：suspension した余極限の反変 Hom の各射影で検査する。
規約：全パラメータの等式であり、頂点別の選択によるものではない。
使われ方：K-7 の全 Raw Hom 極限への持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 元の余極限源の全段の普遍族は、全 Hom の境界条件を満たす。 -/
lemma sequentialHomLimitFamily_condition (D : SpectrumSequence.{u}) (Y : KanSequence.{u})
    (s : Cone (sequentialRawHomDiagram D Y)) (k : ℕ) :
    sequentialHomLimitFamily D Y s (k + 1) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((sequentialLevelColimitSpectrum D).sigma k) (Y.level (k + 1)).space =
        sequentialHomLimitFamily D Y s k ≫
          RawSpectrumMapping.step (sequentialLevelColimitSpectrum D) Y k := by
  let T := tensorLeft PointedSimplicialSet.circle.{u}
  let H := (internalHom (C := PointedSimplicialSet.{u})).flip.obj (Y.level (k + 1)).space
  let c := PointedSimplicialSet.forget.mapCone
    (H.mapCone (T.mapCocone (colimit.cocone (OmegaSpectrum.levelDiagram D k))).op)
  let hc : IsLimit c := isLimitOfPreserves PointedSimplicialSet.forget
    (isLimitOfPreserves H
      (isColimitOfPreserves T (colimit.isColimit (OmegaSpectrum.levelDiagram D k))).op)
  apply hc.hom_ext
  intro a
  have hπ : c.π.app a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (PointedSimplicialSet.circle.{u} ◁ colimit.ι (OmegaSpectrum.levelDiagram D k) a.unop)
        (Y.level (k + 1)).space :=
    (congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre _ _)).symm
  rw [hπ]
  let i := sequentialLevelColimitInjection D a.unop
  have hi : PointedSimplicialSet.circle.{u} ◁ i.app k ≫
      (sequentialLevelColimitSpectrum D).sigma k =
        (D.obj a.unop).sigma k ≫ i.app (k + 1) := i.comm k
  change (sequentialHomLimitFamily D Y s (k + 1) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((sequentialLevelColimitSpectrum D).sigma k) _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ i.app k) _ =
    (sequentialHomLimitFamily D Y s k ≫
      RawSpectrumMapping.step (sequentialLevelColimitSpectrum D) Y k) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ i.app k) _
  calc
    _ = sequentialHomLimitFamily D Y s (k + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ i.app k ≫
          (sequentialLevelColimitSpectrum D).sigma k) _ := by
      rw [sequentialPointedPre_comp, Category.assoc]
    _ = sequentialHomLimitFamily D Y s (k + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((D.obj a.unop).sigma k ≫ i.app (k + 1)) _ :=
      congrArg (fun q ↦ sequentialHomLimitFamily D Y s (k + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre q _) hi
    _ = (sequentialHomLimitFamily D Y s (k + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app (k + 1)) _) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((D.obj a.unop).sigma k) _ := by
      rw [sequentialPointedPre_comp, Category.assoc]
    _ = (s.π.app a ≫ RawSpectrumMapping.evaluation (D.obj a.unop) Y (k + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((D.obj a.unop).sigma k) _ :=
      congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((D.obj a.unop).sigma k) _)
        (sequentialHomLimitFamily_fac D Y s (k + 1) a)
    _ = (s.π.app a ≫ RawSpectrumMapping.evaluation (D.obj a.unop) Y k) ≫
        RawSpectrumMapping.step (D.obj a.unop) Y k := by
      rw [Category.assoc, RawSpectrumMapping.evaluation_condition, ← Category.assoc]
    _ = (sequentialHomLimitFamily D Y s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app k) _) ≫
        RawSpectrumMapping.step (D.obj a.unop) Y k :=
      congrArg (· ≫ RawSpectrumMapping.step (D.obj a.unop) Y k)
        (sequentialHomLimitFamily_fac D Y s k a).symm
    _ = _ := by
      rw [Category.assoc, ← sequentialRawStep_pre, ← Category.assoc]

end SerrePositivity.KST.NonConnective
