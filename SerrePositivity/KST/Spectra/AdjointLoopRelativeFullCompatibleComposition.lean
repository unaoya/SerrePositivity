module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeBoundaryCoordinates
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedWhiskeredSquareComposition

/-!
概要：元の相対 BF 左因子と右射影を同時に保つ全 Hom の組の合成。
方針：左境界は元の BF 豊穣正方形、右境界は各段の実 loop 豊穣正方形で合成する。
規約：右射影の自然性を左因子の可換性だけから推論しない。
使われ方：指定単位・左右因子を保つ全図式の豊穣構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance adjointLoopRelativeFullCompatibleCompositionLocal1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance adjointLoopRelativeFullCompatibleCompositionLocal2 : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：組の左境界は元の BF 全 Hom の豊穣 whiskering の正方形。
方針：普遍族の左境界を元の後合成へ厳密に同定する。
規約：全単体上の元の相対左因子の条件。
使われ方：左境界の合成保存。 -/
lemma full_left_whiskered (X Y : OmegaSpectrum.{u}) :
    fullReplacedMap X Y ≫ eHomWhiskerRight SSet (inclusion X) (middle Y) =
      fullOriginalMap X Y ≫ eHomWhiskerLeft SSet X (inclusion Y) := by
  have h := fullCompatible_left_condition X Y
  rw [inclusionParameterFamily_universal] at h
  change fullReplacedMap X Y ≫
      RawSpectrumMapping.pre (inclusion X) (middle Y).toKanSequence =
    fullOriginalMap X Y ≫ RawSpectrumMapping.post X
      (⟨(inclusion Y).app, (inclusion Y).comm⟩ :
        KanSequence.Hom Y.toKanSequence (middle Y).toKanSequence) at h
  rw [RawSpectrumMapping.pre_spectrum, RawSpectrumMapping.post_spectrum] at h
  exact h

/-- 概要：元の全 Hom の次段へ実 loop の豊穣作用を施した族。
方針：元の射の次段評価へ実内部 Hom の作用を合成する。
規約：元の段評価と通常円を固定する。
使われ方：右射影を保つ全 Hom 正方形の上辺。 -/
def fullOriginalLoopStage (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    fullCompatibleSpace X Y ⟶
      SimplicialCategory.sHom ((target X).level n).space ((target Y).level n).space :=
  fullOriginalMap X Y ≫ evaluation X Y (n + 1) ≫
    (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
      (X.level (n + 1)).space (Y.level (n + 1)).space

/-- 概要：元の置換射の指定段を全 Hom 上で評価する。
方針：実置換射の射影へ元の段評価を合成する。
規約：射のホモトピー類へ移さない。
使われ方：右射影を保つ全 Hom 正方形の下辺。 -/
def fullReplacedStage (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    fullCompatibleSpace X Y ⟶
      SimplicialCategory.sHom ((middle X).level n).space ((middle Y).level n).space :=
  fullReplacedMap X Y ≫ evaluation (middle X) (middle Y) n

/-- 概要：同じ組の右境界は元の段の loop 作用と実右射影の豊穣正方形。
方針：実全 Hom の右境界の式へ普遍族の厳密座標を代入する。
規約：左境界と同じ組の空間で全パラメータを扱う。
使われ方：右境界の合成保存。 -/
lemma full_right_whiskered (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    fullOriginalLoopStage X Y n ≫
        eHomWhiskerRight SSet ((projection X).app n) ((target Y).level n).space =
      fullReplacedStage X Y n ≫
        eHomWhiskerLeft SSet ((middle X).level n).space ((projection Y).app n) := by
  have h := congrArg (· ≫ RawSpectrumMapping.evaluation (middle X) (target Y) n)
    (fullCompatible_right_condition X Y)
  rw [Category.assoc, RawSpectrumMapping.post_evaluation] at h
  have hb := congrArg Under.Hom.right (projectionParameterFamily_universal_evaluation X Y n)
  simp only [Under.comp_right] at hb
  change fullReplacedMap X Y ≫ evaluation (middle X) (middle Y) n ≫
      (PointedObject.basedHomMap ((middle X).level n).space ((projection Y).app n)).right =
    fullOriginalMap X Y ≫
      ((projectionParameterFamily X Y _ (universalParameterHom X Y)).right ≫
        (RawSpectrumMapping.pointedEvaluation (middle X) (target Y) n).right) at h
  rw [hb] at h
  rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq]
  dsimp only [fullOriginalLoopStage, fullReplacedStage, PointedMapping.ihomSimplicialFunctor]
  change (fullOriginalMap X Y ≫
      (RawSpectrumMapping.pointedEvaluation X Y.toKanSequence (n + 1)).right ≫
      (PointedMapping.ihomAction PointedSimplicialSet.circle.{u}
        (X.level (n + 1)).space (Y.level (n + 1)).space).right) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((projection X).app n) ((target Y).level n).space).right =
    (fullReplacedMap X Y ≫ evaluation (middle X) (middle Y) n) ≫
      (PointedObject.basedHomMap ((middle X).level n).space ((projection Y).app n)).right
  simpa only [Category.assoc] using h.symm

/-- 概要：元の射と置換射をそれぞれ元の豊穣合成で合成すると左境界を保つ。
方針：全 Hom の通常境界付き正方形の合成を元の BF 圏へ適用する。
規約：元の相対左因子を変更しない。
使われ方：実 corner への合成の第一射影条件。 -/
lemma full_composition_left_whiskered (X Y Z : OmegaSpectrum.{u}) :
    (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
        mappingComposition (middle X) (middle Y) (middle Z) ≫
          eHomWhiskerRight SSet (inclusion X) (middle Z) =
      (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
        eHomWhiskerLeft SSet X (inclusion Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_comp SSet (inclusion X) (inclusion Y) (inclusion Z)
    (fullReplacedMap X Y) (fullOriginalMap X Y) (fullReplacedMap Y Z) (fullOriginalMap Y Z)
    (full_left_whiskered X Y) (full_left_whiskered Y Z)

/-- 概要：元の射の合成の次段 loop 作用は、二つの元の作用の豊穣合成。
方針：元の段評価の合成則と実内部 Hom 豊穣関手の合成則を使う。
規約：対象ごとの次数同型で代用しない。
使われ方：右境界の全 Hom 合成の照合。 -/
lemma fullOriginalLoopStage_composition (X Y Z : OmegaSpectrum.{u}) (n : ℕ) :
    (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
        evaluation X Z (n + 1) ≫
          (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
            (X.level (n + 1)).space (Z.level (n + 1)).space =
      (fullOriginalLoopStage X Y n ⊗ₘ fullOriginalLoopStage Y Z n) ≫
        eComp SSet ((target X).level n).space ((target Y).level n).space
          ((target Z).level n).space := by
  simp only [mappingComposition_evaluation_assoc, compositionFamily, Category.assoc]
  rw [(PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map_comp]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  rfl

/-- 概要：元の置換射の豊穣合成の段評価は元の二つの段評価の合成。
方針：元の BF 全 Hom の段評価の合成則を使う。
規約：元の置換後の射を保持する。
使われ方：右境界の全 Hom 合成の照合。 -/
lemma fullReplacedStage_composition (X Y Z : OmegaSpectrum.{u}) (n : ℕ) :
    (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
        mappingComposition (middle X) (middle Y) (middle Z) ≫
          evaluation (middle X) (middle Z) n =
      (fullReplacedStage X Y n ⊗ₘ fullReplacedStage Y Z n) ≫
        eComp SSet ((middle X).level n).space ((middle Y).level n).space
          ((middle Z).level n).space := by
  rw [mappingComposition_evaluation]
  dsimp only [compositionFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  rfl

/-- 概要：元の両射影の豊穣合成は元の左境界と厳密可換。
方針：通常の BF 境界付き正方形の合成を実 corner の第一射影へ戻す。
規約：普遍族の左境界を元の射のまま保持する。
使われ方：両境界を保つ組の実合成への持ち上げ。 -/
lemma full_composition_left (X Y Z : OmegaSpectrum.{u}) :
    (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
        mappingComposition (middle X) (middle Y) (middle Z) ≫
          RawSpectrumMapping.pre (inclusion X) (middle Z).toKanSequence =
      (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
        (inclusionParameterFamily X Z _ (universalParameterHom X Z)).right := by
  rw [inclusionParameterFamily_universal]
  change _ = (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
    RawSpectrumMapping.post X (⟨(inclusion Z).app, (inclusion Z).comm⟩ :
      KanSequence.Hom Z.toKanSequence (middle Z).toKanSequence)
  rw [RawSpectrumMapping.pre_spectrum, RawSpectrumMapping.post_spectrum]
  exact full_composition_left_whiskered X Y Z

/-- 概要：同じ両射影の豊穣合成も元の右境界と厳密可換。
方針：各段の実 loop 豊穣正方形を合成し、実普遍族の座標へ戻す。
規約：左境界とは独立に右射影と全 Hom 合成の整合を証明する。
使われ方：両境界を保つ組の実合成への持ち上げ。 -/
lemma full_composition_right (X Y Z : OmegaSpectrum.{u}) :
    (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
        mappingComposition (middle X) (middle Y) (middle Z) ≫
          RawSpectrumMapping.post (middle X) (projection Z) =
      (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
        (projectionParameterFamily X Z _ (universalParameterHom X Z)).right := by
  apply RawSpectrumMapping.hom_ext (middle X) (target Z)
  intro n
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_comp SSet ((projection X).app n)
    ((projection Y).app n) ((projection Z).app n)
    (fullOriginalLoopStage X Y n) (fullReplacedStage X Y n)
    (fullOriginalLoopStage Y Z n) (fullReplacedStage Y Z n)
    (full_right_whiskered X Y n) (full_right_whiskered Y Z n)
  simp only [← Category.assoc] at h
  rw [← fullOriginalLoopStage_composition X Y Z n] at h
  erw [← fullReplacedStage_composition X Y Z n] at h
  rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq] at h
  dsimp only [PointedMapping.ihomSimplicialFunctor] at h
  simp only [Category.assoc, RawSpectrumMapping.post_evaluation]
  change (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
      mappingComposition (middle X) (middle Y) (middle Z) ≫
      evaluation (middle X) (middle Z) n ≫
        (PointedObject.basedHomMap ((middle X).level n).space ((projection Z).app n)).right =
    (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
      ((projectionParameterFamily X Z _ (universalParameterHom X Z)).right ≫
        (RawSpectrumMapping.pointedEvaluation (middle X) (target Z) n).right)
  have hb := congrArg Under.Hom.right (projectionParameterFamily_universal_evaluation X Z n)
  simp only [Under.comp_right] at hb
  rw [hb]
  change (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
      mappingComposition (middle X) (middle Y) (middle Z) ≫ evaluation (middle X) (middle Z) n ≫
      (PointedObject.basedHomMap ((middle X).toKanSequence.level n).space
        ((projection Z).app n)).right =
    (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z ≫
      evaluation X Z (n + 1) ≫
      (PointedMapping.ihomAction PointedSimplicialSet.circle.{u}
        (X.level (n + 1)).space (Z.level (n + 1)).space).right ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((projection X).app n) ((target Z).level n).space
  simpa only [Category.assoc] using h.symm

/-- 概要：元の左右因子を同時に保つ全 Hom の組の実際の豊穣合成。
方針：両射影の元の豊穣合成を、二境界の厳密合成保存で実引き戻しへ持ち上げる。
規約：通常射だけの合成法則に弱めない。
使われ方：相対 BF 置換の指定単位・右射影を保つ全図式の構成。 -/
def fullCompatibleComposition (X Y Z : OmegaSpectrum.{u}) :
    fullCompatibleSpace X Y ⊗ fullCompatibleSpace Y Z ⟶ fullCompatibleSpace X Z :=
  pullback.lift
    ((fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
      mappingComposition (middle X) (middle Y) (middle Z))
    ((fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z) (by
      apply pullback.hom_ext
      · simpa only [Category.assoc, RawSpectrumMapping.relativeCorner_fst,
          fullBoundaryMap_fst] using full_composition_left X Y Z
      · simpa only [Category.assoc, RawSpectrumMapping.relativeCorner_snd,
          fullBoundaryMap_snd] using full_composition_right X Y Z)

/-- 概要：組の合成の置換射影は元の置換射の豊穣合成。
方針：実引き戻しへの持ち上げの第一射影式を使う。
規約：元の BF 射を保持する。
使われ方：全 Hom の合成の圏の法則。 -/
@[reassoc (attr := simp)]
lemma fullCompatibleComposition_replacedMap (X Y Z : OmegaSpectrum.{u}) :
    fullCompatibleComposition X Y Z ≫ fullReplacedMap X Z =
      (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z) ≫
        mappingComposition (middle X) (middle Y) (middle Z) :=
  pullback.lift_fst _ _ _

/-- 概要：組の合成の元の射への射影は元の豊穣合成。
方針：実引き戻しへの持ち上げの第二射影式を使う。
規約：元の全 Hom パラメータを保持する。
使われ方：全 Hom の合成の圏の法則。 -/
@[reassoc (attr := simp)]
lemma fullCompatibleComposition_originalMap (X Y Z : OmegaSpectrum.{u}) :
    fullCompatibleComposition X Y Z ≫ fullOriginalMap X Z =
      (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z) ≫ mappingComposition X Y Z :=
  pullback.lift_snd _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
