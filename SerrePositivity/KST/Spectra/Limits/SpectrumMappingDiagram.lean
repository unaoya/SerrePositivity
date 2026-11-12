module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits
public import SerrePositivity.KST.Spectra.CoherentNerve
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：L9 の実際の Ω スペクトルの写像空間と各段の点つき写像空間の自然性。
方針：L9 の厳密な単体的合成を各段で評価し、後合成を点つき内部 Hom の作用に同定する。
規約：L9 の対象と豊穣構造をそのまま用いる。別の Sp の模型は定義しない。
使われ方：HTT 4.2.4.1、BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB） の Sp の Hom の極限条件の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits

noncomputable section

local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：Ω スペクトルを指定段の点つき単体集合へ送る評価関手。
方針：対象は level、射は厳密な射の app を使う。
規約：L9 の元の点つき圏へ値を取る。
使われ方：BF 1978 §2、γ3c の段ごとの極限の普遍性の指定。 -/
def spectrumLevelFunctor (n : ℕ) : OmegaSpectrum.{u} ⥤ PointedSimplicialSet.{u} where
  obj Y := (Y.level n).space
  map f := f.app n

/-- 概要：始域を固定した点つき写像単体集合の共変関手。
方針：点つき内部 Hom 関手に基点の忘却を合成する。
規約：パラメータの単体集合には基点を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の段ごとの Hom の極限の計算。 -/
noncomputable def pointedMappingFunctor (A : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u} ⥤ SSet.{u} :=
  PointedObject.basedHomFunctor A ⋙ PointedSimplicialSet.forget

/-- 概要：点つき写像単体集合の関手は全ての極限を保存する。
方針：smash と内部 Hom、自由基点と忘却の二つの随伴を合成する。
規約：元の点つき対象の Kan 性を仮定しない。
使われ方：HTT 4.2.4.1 の Sp の Hom の極限条件を段ごとに検証する。 -/
noncomputable instance pointedMappingFunctor_preservesLimits (A : PointedSimplicialSet.{u}) :
    PreservesLimits (pointedMappingFunctor A) := by
  have : (PointedObject.basedHomFunctor A).IsRightAdjoint :=
    (PointedSimplicialSet.smashHomAdjunction A).isRightAdjoint
  have : PointedSimplicialSet.forget.{u}.IsRightAdjoint :=
    PointedObject.adjoinForgetAdjunction.isRightAdjoint
  exact inferInstanceAs
    (PreservesLimits (PointedObject.basedHomFunctor A ⋙ PointedSimplicialSet.forget))

/-- 概要：スペクトルの射による Hom の後合成を指定段で評価するとその段の後合成になる。
方針：L9 の合成の評価式と通常の射の頂点の評価を使い、右単位子の自然性でまとめる。
規約：実際の L9 の写像単体集合の射の厳密な等式。
使われ方：BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB） の Hom 図式と段評価の可換性。 -/
lemma spectrumHomMap_evaluation (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (f : Y ⟶ Z) (n : ℕ) :
    ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map f ≫
        OmegaSpectrum.evaluation X Z n =
      OmegaSpectrum.evaluation X Y n ≫
        (PointedObject.basedHomMap (X.level n).space (f.app n)).right := by
  have hf : eHomEquiv SSet f = OmegaSpectrum.vertexOfHomMap f := by
    change (SSet.unitHomEquiv (OmegaSpectrum.mappingSpace Y Z)).symm
      ((SSet.unitHomEquiv _ ) (OmegaSpectrum.vertexOfHomMap f)) = _
    exact Equiv.symm_apply_apply _ _
  change eHomWhiskerLeft SSet X f ≫ OmegaSpectrum.evaluation X Z n = _
  unfold eHomWhiskerLeft
  rw [hf]
  simp only [Category.assoc]
  change (ρ_ (OmegaSpectrum.mappingSpace X Y)).inv ≫
    OmegaSpectrum.mappingSpace X Y ◁ OmegaSpectrum.vertexOfHomMap f ≫
      OmegaSpectrum.mappingComposition X Y Z ≫ OmegaSpectrum.evaluation X Z n = _
  rw [OmegaSpectrum.mappingComposition_evaluation]
  unfold OmegaSpectrum.compositionFamily
  rw [whiskerLeft_comp_tensorHom_assoc, OmegaSpectrum.vertexOfHomMap_evaluation,
    rightUnitor_inv_comp_tensorHom_assoc]
  change OmegaSpectrum.evaluation X Y n ≫
    eHomWhiskerLeft SSet (X.level n).space (f.app n) = _
  rw [PointedEnrichment.whiskerLeft_eq]

/-- 概要：スペクトルの段ごとの点つき Hom の図式。
方針：指定段の評価と点つき写像空間の関手を合成する。
規約：始域のスペクトル X と段 n を固定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） のスペクトルの Hom の極限を検査する各段の図式。 -/
noncomputable def spectrumStageHomFunctor (X : OmegaSpectrum.{u}) (n : ℕ) :
    OmegaSpectrum.{u} ⥤ SSet.{u} :=
  spectrumLevelFunctor n ⋙ pointedMappingFunctor (X.level n).space

/-- 概要：スペクトルの写像空間から各段の点つき写像空間への自然変換。
方針：L9 の評価を成分とし、後合成と段評価の可換式を使う。
規約：各成分は元の OmegaSpectrum.evaluation そのもの。
使われ方：HTT 4.2.4.1 の Sp の Hom 錐を段ごとの錐へ展開する。 -/
noncomputable def spectrumMappingEvaluation (X : OmegaSpectrum.{u}) (n : ℕ) :
    (SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X) ⟶
      spectrumStageHomFunctor X n where
  app Y := OmegaSpectrum.evaluation X Y n
  naturality _Y _Z f := spectrumHomMap_evaluation X f n

/-- 概要：点つき Hom の前合成と後合成は可換。
方針：通常の豊穣圏の二変数の自然性を点つき Hom の具体的な射へ移す。
規約：点つき対象の Kan 性は要求しない。
使われ方：BF 1978 §2、各段の普遍族の境界条件の検証。 -/
lemma pointedMapping_pre_post {A B Y Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (f : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y ≫ (pointedMappingFunctor A).map f =
      (pointedMappingFunctor B).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z := by
  have h := eHom_whisker_exchange SSet i f
  simp only [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq] at h
  exact h.symm

/-- 概要：懸垂の写像空間への作用は標的の後合成と可換。
方針：smash の閉構造で uncurry し、結合子と評価の自然性を使う。
規約：全ての点つき対象と射で成り立つ。
使われ方：BF 1978 §2、スペクトルの各段の普遍族の構造整合性。 -/
lemma suspensionHom_post (A : PointedSimplicialSet.{u}) {B D : PointedSimplicialSet.{u}}
    (f : B ⟶ D) :
    (pointedMappingFunctor A).map f ≫ (suspensionHom A D).right =
      (suspensionHom A B).right ≫ (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map
        (PointedSimplicialSet.circle.{u} ◁ f) := by
  have h : (ihom A).map f ≫ suspensionHom A D =
      suspensionHom A B ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map (PointedSimplicialSet.circle.{u} ◁ f) := by
    have hev := (ihom.ev A).naturality f
    change (A ◁ (ihom A).map f) ≫ (ihom.ev A).app D = (ihom.ev A).app B ≫ f at hev
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right,
      suspensionHom, MonoidalClosed.uncurry_curry, suspensionHom,
      MonoidalClosed.uncurry_curry]
    change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A ◁ (ihom A).map f) ≫
        (α_ PointedSimplicialSet.circle.{u} A ((ihom A).obj D)).hom ≫
          PointedSimplicialSet.circle.{u} ◁ (ihom.ev A).app D = _
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp,
      hev, whiskerLeft_comp, Category.assoc]
  exact congrArg Under.Hom.right h

/-- 概要：スペクトルの境界比較は標的のスペクトル射による後合成と可換。
方針：懸垂の写像空間の自然性とスペクトル射の構造射との可換条件を使う。
規約：Ω 条件と構造射の単射性は証明に使わない。
使われ方：BF 1978 §2、段ごとの極限の普遍族を全写像空間へ束ねる条件。 -/
lemma spectrumMappingStep_post (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (f : Y ⟶ Z) (n : ℕ) :
    OmegaSpectrum.mappingStep X Y n ≫
        (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (f.app (n + 1)) =
      (pointedMappingFunctor (X.level n).space).map (f.app n) ≫
        OmegaSpectrum.mappingStep X Z n := by
  change ((suspensionHom (X.level n).space (Y.level n).space).right ≫
    (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (Y.sigma n)) ≫ _ =
    _ ≫ (suspensionHom (X.level n).space (Z.level n).space).right ≫
      (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (Z.sigma n)
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← f.comm,
    CategoryTheory.Functor.map_comp, ← Category.assoc, ← suspensionHom_post, Category.assoc]

end

end SerrePositivity.InfinityCategories.HomotopyLimits
