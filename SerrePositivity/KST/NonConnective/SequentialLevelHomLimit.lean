module

public import SerrePositivity.KST.NonConnective.SequentialLevelColimitUniversal
public import SerrePositivity.KST.NonConnective.SequentialRawHomDiagram
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition

/-!
概要：逐次 BF 余極限の各段における、全反変 Hom の厳密な極限。
方針：点つき内部 Hom の反変変数の極限保存を、元の段の余極限へ適用する。
規約：Kan 性だけから homotopy 極限性を結論しない。
使われ方：同じ余錐の ∞ 普遍性に向かう全 Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 固定標的の一段への反変な点つき Hom 図式の台。 -/
abbrev sequentialLevelHomDiagram (D : SpectrumSequence.{u}) (Y : KanSequence.{u}) (k : ℕ) :=
  (OmegaSpectrum.levelDiagram D k).op ⋙
    (internalHom (C := PointedSimplicialSet.{u})).flip.obj (Y.level k).space ⋙
      PointedSimplicialSet.forget

/-- 元の段の余極限の反対の Hom 錐。 -/
def sequentialLevelHomCone (D : SpectrumSequence.{u}) (Y : KanSequence.{u}) (k : ℕ) :
    Cone (sequentialLevelHomDiagram D Y k) :=
  PointedSimplicialSet.forget.mapCone
    (((internalHom (C := PointedSimplicialSet.{u})).flip.obj (Y.level k).space).mapCone
      (colimit.cocone (OmegaSpectrum.levelDiagram D k)).op)

/-- 元の同じ段の Hom 錐は単体集合の通常の極限。 -/
def sequentialLevelHomIsLimit (D : SpectrumSequence.{u}) (Y : KanSequence.{u}) (k : ℕ) :
    IsLimit (sequentialLevelHomCone D Y k) :=
  isLimitOfPreserves PointedSimplicialSet.forget
    (isLimitOfPreserves ((internalHom (C := PointedSimplicialSet.{u})).flip.obj
      (Y.level k).space) (colimit.isColimit (OmegaSpectrum.levelDiagram D k)).op)

/-- スペクトルの全 Raw Hom の段評価は、反変 Hom 図式の自然変換。 -/
def sequentialRawHomEvaluation (D : SpectrumSequence.{u}) (Y : KanSequence.{u}) (k : ℕ) :
    sequentialRawHomDiagram D Y ⟶ sequentialLevelHomDiagram D Y k where
  app a := RawSpectrumMapping.evaluation (D.obj a.unop) Y k
  naturality a b f := by
    change RawSpectrumMapping.pre (D.map f.unop) Y ≫
      RawSpectrumMapping.evaluation (D.obj b.unop) Y k =
        RawSpectrumMapping.evaluation (D.obj a.unop) Y k ≫
          ((MonoidalClosed.pre ((D.map f.unop).app k)).app (Y.level k).space).right
    exact (RawSpectrumMapping.pre_evaluation (D.map f.unop) Y k).trans
      (congrArg (RawSpectrumMapping.evaluation (D.obj a.unop) Y k ≫ ·)
        (congrArg Under.Hom.right
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre ((D.map f.unop).app k) (Y.level k).space)))

/-- 全 Raw Hom 図式の厳密錐から、余極限源の一段への普遍 Hom 族を取る。 -/
def sequentialHomLimitFamily (D : SpectrumSequence.{u}) (Y : KanSequence.{u})
    (s : Cone (sequentialRawHomDiagram D Y)) (k : ℕ) :
    s.pt ⟶ (PointedObject.basedHom
      ((sequentialLevelColimitSpectrum D).level k).space (Y.level k).space).right :=
  (sequentialLevelHomIsLimit D Y k).lift
    ((Cone.postcompose (sequentialRawHomEvaluation D Y k)).obj s)

/-- 同じ一段の Hom 族は、各入力段へ制限すると元の錐の段評価になる。 -/
lemma sequentialHomLimitFamily_fac (D : SpectrumSequence.{u}) (Y : KanSequence.{u})
    (s : Cone (sequentialRawHomDiagram D Y)) (k : ℕ) (a : SequentialIndex.{u}ᵒᵖ) :
    sequentialHomLimitFamily D Y s k ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (colimit.ι (OmegaSpectrum.levelDiagram D k) a.unop)
        (Y.level k).space).right =
          s.π.app a ≫ RawSpectrumMapping.evaluation (D.obj a.unop) Y k := by
  have h := (sequentialLevelHomIsLimit D Y k).fac
    ((Cone.postcompose (sequentialRawHomEvaluation D Y k)).obj s) a
  change sequentialHomLimitFamily D Y s k ≫
    ((MonoidalClosed.pre (colimit.ι (OmegaSpectrum.levelDiagram D k) a.unop)).app
      (Y.level k).space).right = _ at h
  exact (congrArg (fun q ↦ sequentialHomLimitFamily D Y s k ≫ q.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre
      (colimit.ι (OmegaSpectrum.levelDiagram D k) a.unop) (Y.level k).space)).trans h

end SerrePositivity.KST.NonConnective
