module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitIntervalCoordinates

/-!
概要：源単位のパラメータ付き列射の区間を、元の Kan 随伴右側の評価区間へ照合する。
方針：符号付き loop 列射の転置を内部 Hom の作用で表示する。
規約：同じ実辺全体の一致。使われ方：源単位三角形を元の段評価区間へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra
namespace PointedMapping.VerticalPath

/-- 源作用へ追加のパラメータを制限しても、同じ前合成された入力の実辺を保つ。 -/
lemma basedPreAction_pre_path {W D C A T B : PointedSimplicialSet.{u}}
    {f g : W ⟶ D} (H : VerticalPath (PointedObject.toPoint D) f g)
    (r : A ⟶ PointedObject.basedHom D C) (a : T ⟶ A) (b : B ⟶ T) :
    ((H.basedPreAction r a).pre b).path = (H.basedPreAction r (b ≫ a)).path := by
  change (((H.basedPre C).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom W C)).right) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a (PointedObject.basedHom W C)).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b (PointedObject.basedHom W C)).right = _
  change (((H.basedPre C).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom W C)).right) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a (PointedObject.basedHom W C)).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b (PointedObject.basedHom W C)).right =
    ((H.basedPre C).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom W C)).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (b ≫ a) (PointedObject.basedHom W C)).right
  have h := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp b a (PointedObject.basedHom W C))
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun k => ((H.basedPre C).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom W C)).right) ≫ k) h

end PointedMapping.VerticalPath
namespace RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 符号付き loop 列射の各段の転置は、元の次段評価への同じ内部 Hom 作用。 -/
lemma signedLoopParameterHom_transpose (n : ℕ) :
    PointedMapping.transpose ((KanSequence.signedLoopParameterHom
      (homOfParameterFamily X Y.toKanSequence A φ)).app n) =
    (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1)) ≫
      PointedMapping.ihomAction CirclePower.space.{u}
        (X.level (n + 1)).space (Y.level (n + 1)).space := by
  rw [KanSequence.signedLoopParameterHom_app, homOfParameterFamily_app]
  have h := PointedMapping.transpose_ihomParameterAction
    (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1))
    (𝟙 (PointedObject.basedHom CirclePower.space.{u} (X.level (n + 1)).space))
  have hid : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
      (𝟙 (PointedObject.basedHom CirclePower.space.{u} (X.level (n + 1)).space))
      (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space) = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact congrArg (fun t => t.app _)
      (MonoidalClosed.pre_id
        (PointedObject.basedHom CirclePower.space.{u} (X.level (n + 1)).space))
  erw [hid] at h
  simp only [PointedObject.ihom_obj_eq_basedHom, Category.id_comp] at h
  exact h

/-- 元の源単位評価区間は、保存済みの同じ前合成作用の辺を保持する。 -/
lemma kanAdjointTracedSourceEvaluationInterval_path (n : ℕ) :
    (OmegaSpectrum.CotensorCompatible.kanAdjointTracedSourceEvaluationInterval X Y n).path =
      ((OmegaSpectrum.tracedSignedLoopUnitComparison X n).basedPreAction
        (PointedMapping.ihomAction CirclePower.space.{u}
          (X.level (n + 1)).space (Y.level (n + 1)).space)
        (pointedEvaluation X Y.toKanSequence (n + 1))).path := rfl

/-- 同じ列射への後合成・転置区間は、元の源単位評価区間と辺全体で一致する。 -/
lemma tracedSourceUnitStageInterval_path (n : ℕ) :
    (tracedSourceUnitStageInterval X Y φ n).path =
      ((OmegaSpectrum.CotensorCompatible.kanAdjointTracedSourceEvaluationInterval X Y n).pre
        φ).path := by
  let H := OmegaSpectrum.tracedSignedLoopUnitComparison X n
  let r := PointedMapping.ihomAction CirclePower.space.{u}
    (X.level (n + 1)).space (Y.level (n + 1)).space
  let a := pointedEvaluation X Y.toKanSequence (n + 1)
  change ((H.basedPost _).basedTranspose).path =
    (OmegaSpectrum.CotensorCompatible.kanAdjointTracedSourceEvaluationInterval X Y n).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed φ _).right
  rw [kanAdjointTracedSourceEvaluationInterval_path]
  change ((H.basedPost _).basedTranspose).path = ((H.basedPreAction r a).pre φ).path
  rw [PointedMapping.VerticalPath.basedPreAction_pre_path,
    PointedMapping.VerticalPath.basedPreAction_post_transpose_path]
  have ht := congrArg PointedMapping.transpose (signedLoopParameterHom_transpose X Y φ n)
  rw [PointedMapping.transpose_transpose] at ht
  rw [← ht]

/-- 源三角形の対角辺も、元の次段の源単位評価区間の構造制限に厳密一致する。 -/
lemma tracedSourceUnitParameterTriangle_one_evaluation (n : ℕ) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      (((OmegaSpectrum.CotensorCompatible.kanAdjointTracedSourceEvaluationInterval
        X Y (n + 1)).pre φ).basedPost
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
            ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
  rw [tracedSourceUnitParameterTriangle_one_stage]
  change (tracedSourceUnitStageInterval X Y φ (n + 1)).path ≫ _ = _
  rw [tracedSourceUnitStageInterval_path]
  rfl

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
