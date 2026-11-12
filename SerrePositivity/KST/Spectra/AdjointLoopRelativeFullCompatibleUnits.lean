module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCompatibleComposition

/-!
概要：元の左右因子を同時に保つ全 Hom の組の恒等射。
方針：左右境界の全段座標と実 loop 豊穣関手の単位保存で、元の二恒等射を持ち上げる。
規約：恒等射を選び直した比較射で代用しない。
使われ方：相対 BF の指定単位・右射影を保つ豊穣圏の単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance adjointLoopRelativeFullCompatibleUnitsLocal1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance adjointLoopRelativeFullCompatibleUnitsLocal2 : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：元の二恒等射は指定相対左因子を厳密に保つ。
方針：元の BF 豊穣恒等正方形を適用する。
規約：全 Hom の元の恒等射を使う。
使われ方：組の恒等射の左境界。 -/
lemma full_identity_left (X : OmegaSpectrum.{u}) :
    mappingIdentity (middle X) ≫
        RawSpectrumMapping.pre (inclusion X) (middle X).toKanSequence =
      mappingIdentity X ≫
        (inclusionParameterFamily X X _ (universalParameterHom X X)).right := by
  rw [inclusionParameterFamily_universal]
  change mappingIdentity (middle X) ≫
      RawSpectrumMapping.pre (inclusion X) (middle X).toKanSequence =
    mappingIdentity X ≫ RawSpectrumMapping.post X
      (⟨(inclusion X).app, (inclusion X).comm⟩ :
        KanSequence.Hom X.toKanSequence (middle X).toKanSequence)
  rw [RawSpectrumMapping.pre_spectrum, RawSpectrumMapping.post_spectrum]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_id SSet (inclusion X)

/-- 概要：同じ二恒等射は指定相対右射影も厳密に保つ。
方針：全段座標と実 loop 豊穣関手の単位保存を通常の恒等正方形へ戻す。
規約：元の右射影を変更しない。
使われ方：組の恒等射の右境界。 -/
lemma full_identity_right (X : OmegaSpectrum.{u}) :
    mappingIdentity (middle X) ≫ RawSpectrumMapping.post (middle X) (projection X) =
      mappingIdentity X ≫
        (projectionParameterFamily X X _ (universalParameterHom X X)).right := by
  apply RawSpectrumMapping.hom_ext (middle X) (target X)
  intro n
  simp only [Category.assoc, RawSpectrumMapping.post_evaluation]
  change mappingIdentity (middle X) ≫ evaluation (middle X) (middle X) n ≫
      (PointedObject.basedHomMap ((middle X).level n).space ((projection X).app n)).right =
    mappingIdentity X ≫
      ((projectionParameterFamily X X _ (universalParameterHom X X)).right ≫
        (RawSpectrumMapping.pointedEvaluation (middle X) (target X) n).right)
  have hb := congrArg Under.Hom.right (projectionParameterFamily_universal_evaluation X X n)
  simp only [Under.comp_right] at hb
  rw [hb]
  have hid := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_id SSet ((projection X).app n)).symm
  rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq] at hid
  change mappingIdentity (middle X) ≫ evaluation (middle X) (middle X) n ≫
      (PointedObject.basedHomMap ((middle X).level n).space ((projection X).app n)).right =
    mappingIdentity X ≫ evaluation X X (n + 1) ≫
      (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
        (X.level (n + 1)).space (X.level (n + 1)).space ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((projection X).app n) ((target X).level n).space
  rw [mappingIdentity_evaluation_assoc, mappingIdentity_evaluation_assoc]
  have hm := (PointedMapping.ihomSimplicialFunctor
    PointedSimplicialSet.circle.{u}).map_id (X.level (n + 1)).space
  have hm' := congrArg (fun k ↦ k ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((projection X).app n) ((target X).level n).space) hm
  have hh : eId SSet ((target X).level n).space =
      eId SSet ((PointedMapping.ihomSimplicialFunctor
        PointedSimplicialSet.circle.{u}).obj (X.level (n + 1)).space) := by
    simp only [target, KanSequence.adjointLoop, KanSequence.mapping, KanSequence.tail,
      PointedObject.ihom_obj_eq_basedHom, PointedMapping.ihomSimplicialFunctor]
    rfl
  exact hid.trans (by rw [hh]; simpa only [Category.assoc] using hm'.symm)

/-- 概要：左右の指定境界を同時に保つ全 Hom の組の実恒等射。
方針：元の二恒等射を二境界の厳密可換性で実引き戻しへ持ち上げる。
規約：選択した別の自己射を使わない。
使われ方：相対 BF 全 Hom の豊穣単位。 -/
def fullCompatibleIdentity (X : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ fullCompatibleSpace X X :=
  pullback.lift (mappingIdentity (middle X)) (mappingIdentity X) (by
    apply pullback.hom_ext
    · simpa only [Category.assoc, RawSpectrumMapping.relativeCorner_fst,
        fullBoundaryMap_fst] using full_identity_left X
    · simpa only [Category.assoc, RawSpectrumMapping.relativeCorner_snd,
        fullBoundaryMap_snd] using full_identity_right X)

/-- 概要：組の実恒等射の置換射影は元の恒等射。
方針：実引き戻しの第一射影式を使う。
規約：元の BF 対象の恒等射を保持する。
使われ方：全 Hom の単位法則。 -/
@[reassoc (attr := simp)]
lemma fullCompatibleIdentity_replacedMap (X : OmegaSpectrum.{u}) :
    fullCompatibleIdentity X ≫ fullReplacedMap X X = mappingIdentity (middle X) :=
  pullback.lift_fst _ _ _

/-- 概要：組の実恒等射の元の射への射影も元の恒等射。
方針：実引き戻しの第二射影式を使う。
規約：元の全 Hom を保持する。
使われ方：全 Hom の単位法則。 -/
@[reassoc (attr := simp)]
lemma fullCompatibleIdentity_originalMap (X : OmegaSpectrum.{u}) :
    fullCompatibleIdentity X ≫ fullOriginalMap X X = mappingIdentity X :=
  pullback.lift_snd _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
