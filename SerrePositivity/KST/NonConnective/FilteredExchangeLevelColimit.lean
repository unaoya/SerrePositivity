module
public import SerrePositivity.KST.NonConnective.SequentialComparison
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
概要：K-7 の filtered/逐次交換に用いる段別 BF 余極限を、任意の小 filtered 添字で構成する。
方針：既存の逐次証明と同じ filtered 単射保存・段別普遍射を、外側添字にも適用する。
規約：通常 BF 圏の余極限。一般 filtered Sp ∞ 余極限性はここでは主張しない。
使われ方：e の二つの実 BF 実現の交換と、既存候補への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective.FilteredExchange
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 段ごとの filtered Kan 余極限の構造射も単射である。 -/
lemma kanSequence_sigma_mono (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    Mono ((OmegaSpectrum.filteredKanSequence D).sigma k).right := by
  let T := tensorLeft PointedSimplicialSet.circle.{u}
  let U := PointedSimplicialSet.forget
  let c := U.mapCocone (T.mapCocone (colimit.cocone (OmegaSpectrum.levelDiagram D k)))
  let d := U.mapCocone (colimit.cocone (OmegaSpectrum.levelDiagram D (k + 1)))
  let hc : IsColimit c := isColimitOfPreserves U
    (isColimitOfPreserves T (colimit.isColimit (OmegaSpectrum.levelDiagram D k)))
  let hd : IsColimit d := isColimitOfPreserves U
    (colimit.isColimit (OmegaSpectrum.levelDiagram D (k + 1)))
  let t := Functor.whiskerRight (OmegaSpectrum.structureTransformation D k) U
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.monomorphisms SSet.{u}) _ _ c d hc hd t
    (fun a ↦ (D.obj a).sigma_mono k) ((OmegaSpectrum.filteredKanSequence D).sigma k).right
    (fun a ↦ congrArg Under.Hom.right ((OmegaSpectrum.filteredKanInjection D a).comm k))

/-- 単射条件も持つ、置換前の段ごとの余極限 BF 対象。 -/
def levelColimitSpectrum (D : J ⥤ OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (OmegaSpectrum.filteredKanSequence D).toOmegaSpectrum
    (kanSequence_sigma_mono D) (OmegaSpectrum.filteredKanSequence_omegaCondition D)

/-- 段ごとの標準注入は置換前の BF 対象への厳密射でもある。 -/
def levelColimitInjection (D : J ⥤ OmegaSpectrum.{u}) (a : J) :
    D.obj a ⟶ levelColimitSpectrum D where
  app := (OmegaSpectrum.filteredKanInjection D a).app
  comm := (OmegaSpectrum.filteredKanInjection D a).comm

/-- 元の BF 図式に対する、段ごとの余極限を頂点とする厳密な通常余錐。 -/
def levelColimitCocone (D : J ⥤ OmegaSpectrum.{u}) : Cocone D where
  pt := levelColimitSpectrum D
  ι := {
    app := levelColimitInjection D
    naturality _ _ f := by
      apply OmegaSpectrum.Hom.ext
      intro k
      exact colimit.w (OmegaSpectrum.levelDiagram D k) f }

/-- 既存の BF 置換から、置換前の BF 余極限への同じ射影。 -/
def replacementProjection (D : J ⥤ OmegaSpectrum.{u}) :
    OmegaSpectrum.filteredOmegaSpectrum D ⟶ levelColimitSpectrum D where
  app := (OmegaSpectrum.filteredSequenceComparison D).app
  comm := (OmegaSpectrum.filteredSequenceComparison D).comm

/-- 上の同じ実射影は全整数の π 同型。 -/
lemma replacementProjection_piIsomorphism (D : J ⥤ OmegaSpectrum.{u}) :
    OmegaSpectrum.PiIsomorphism (replacementProjection D) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (OmegaSpectrum.filteredLevelComparison_piIsomorphism D)

/-- 任意の厳密な BF 余錐へ、各段で余極限の普遍射を取った実 BF 射。 -/
def levelColimitDesc (D : J ⥤ OmegaSpectrum.{u}) (s : Cocone D) :
    levelColimitSpectrum D ⟶ s.pt where
  app k := colimit.desc (OmegaSpectrum.levelDiagram D k)
    ((OmegaSpectrum.levelEvaluation k).mapCocone s)
  comm k := by
    apply (isColimitOfPreserves (tensorLeft PointedSimplicialSet.circle.{u})
      (colimit.isColimit (OmegaSpectrum.levelDiagram D k))).hom_ext
    intro a
    change (PointedSimplicialSet.circle.{u} ◁ colimit.ι (OmegaSpectrum.levelDiagram D k) a) ≫
      ((PointedSimplicialSet.circle.{u} ◁ colimit.desc (OmegaSpectrum.levelDiagram D k)
        ((OmegaSpectrum.levelEvaluation k).mapCocone s)) ≫ s.pt.sigma k) =
      (PointedSimplicialSet.circle.{u} ◁ colimit.ι (OmegaSpectrum.levelDiagram D k) a) ≫
        ((OmegaSpectrum.filteredKanSequence D).sigma k ≫
          colimit.desc (OmegaSpectrum.levelDiagram D (k + 1))
            ((OmegaSpectrum.levelEvaluation (k + 1)).mapCocone s))
    rw [← Category.assoc, ← whiskerLeft_comp, colimit.ι_desc]
    change PointedSimplicialSet.circle.{u} ◁ (s.ι.app a).app k ≫ s.pt.sigma k = _
    have hs : PointedSimplicialSet.circle.{u} ◁ (s.ι.app a).app k ≫ s.pt.sigma k =
        (D.obj a).sigma k ≫ (s.ι.app a).app (k + 1) := (s.ι.app a).comm k
    have hd := (OmegaSpectrum.filteredKanInjection D a).comm k
    have hi : colimit.ι (OmegaSpectrum.levelDiagram D (k + 1)) a ≫
        colimit.desc (OmegaSpectrum.levelDiagram D (k + 1))
          ((OmegaSpectrum.levelEvaluation (k + 1)).mapCocone s) =
            (s.ι.app a).app (k + 1) := colimit.ι_desc _ a
    exact hs.trans (((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ colimit.desc (OmegaSpectrum.levelDiagram D (k + 1))
        ((OmegaSpectrum.levelEvaluation (k + 1)).mapCocone s)) hd).trans
          ((Category.assoc _ _ _).trans (congrArg ((D.obj a).sigma k ≫ ·) hi)))).symm)


/-- 段ごとの余錐は厳密な BF 射の通常の圏で余極限。 -/
def levelColimitIsColimit (D : J ⥤ OmegaSpectrum.{u}) :
    IsColimit (levelColimitCocone D) where
  desc := levelColimitDesc D
  fac s a := by
    apply OmegaSpectrum.Hom.ext
    intro k
    exact colimit.ι_desc ((OmegaSpectrum.levelEvaluation k).mapCocone s) a
  uniq s m hm := by
    apply OmegaSpectrum.Hom.ext
    intro k
    apply colimit.hom_ext
    intro a
    have h := congrArg (fun f ↦ f.app k) (hm a)
    exact h.trans (colimit.ι_desc ((OmegaSpectrum.levelEvaluation k).mapCocone s) a).symm


end SerrePositivity.KST.NonConnective.FilteredExchange
