module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitTriangleAction
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitRestriction
public import SerrePositivity.KST.Spectra.PointedIntervalNaturality

/-!
概要：源単位の同じ次段区間と、その構造射への制限の全パラメータ座標。
方針：後合成・源制限・転置の厳密な自然性を区間の辺全体に適用する。
規約：区間の再選択なし。使われ方：源単位の実三角形の対角境界の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra
namespace PointedMapping.VerticalPath

/-- 外側の源への制限を転置すると、同じ内側の源への制限になる。 -/
lemma basedTranspose_pre_outer_path {U W A C : PointedSimplicialSet.{u}}
    {f g : U ⟶ PointedObject.basedHom A C}
    (H : VerticalPath (PointedObject.toPoint _) f g) (i : W ⟶ U) :
    ((H.pre i).basedTranspose).path =
      (H.basedTranspose.basedPost (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i C)).path := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left i A C
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, PointedObject.ihom_obj_eq_basedHom] at hn
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom A C) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W A C).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U A C).hom ≫ PointedObject.basedHomMap A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i C) at hn
  change (H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom A C)).right) ≫ _ =
    (H.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U A C).hom.right) ≫ _
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun k => H.path ≫ k.right) hn

end PointedMapping.VerticalPath
namespace RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の源単位の比較区間を、同じパラメータ付き列射へ後合成して転置する。 -/
def tracedSourceUnitStageInterval (n : ℕ) :=
  ((OmegaSpectrum.tracedSignedLoopUnitComparison X n).basedPost
    ((KanSequence.signedLoopParameterHom
      (homOfParameterFamily X Y.toKanSequence A φ)).app n)).basedTranspose

/-- 源三角形の対角辺は、同じ次段区間を元の構造射へ制限した辺そのもの。 -/
lemma tracedSourceUnitParameterTriangle_one_stage (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      ((tracedSourceUnitStageInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
  rw [tracedSourceUnitParameterTriangle_one,
    PointedMapping.VerticalPath.basedPreAction_action_path]
  change (OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval X n).path ≫
    (tracedSourceUnitStructureAction X Y φ n).right = _
  rw [tracedSourceUnitStructureAction_post,
    OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval_path]
  let H := OmegaSpectrum.tracedSignedLoopUnitComparison X (n + 1)
  let p := (KanSequence.signedLoopParameterHom
    (homOfParameterFamily X Y.toKanSequence A φ)).app (n + 1)
  have hp := PointedMapping.VerticalPath.pre_basedPost_path H (X.sigma n) p
  have ht := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
    ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right) hp.symm
  change (((H.pre (X.sigma n)).basedPost p).basedTranspose).path =
    (((H.basedPost p).pre (X.sigma n)).basedTranspose).path at ht
  change (((H.pre (X.sigma n)).basedPost p).basedTranspose).path = _
  exact ht.trans ((H.basedPost p).basedTranspose_pre_outer_path (X.sigma n))

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
