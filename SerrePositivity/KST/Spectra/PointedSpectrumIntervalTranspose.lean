module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingExchange
public import SerrePositivity.KST.Spectra.PointedIhomStepInterval
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry

/-!
概要：全パラメータの実区間の転置を列の構造像と制限へ照合する。
方針：内部 Hom の交換の逆向きの自然性を同じ区間全体へ後合成する。
規約：頂点だけでなく区間の射の等式。使われ方：単位の評価正方形の段射座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 全パラメータから段射への交換も、構造像と厳密に可換。 -/
lemma step_exchange_transpose (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    (ihom A).map (pointedStep X Y n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        (Y.level (n + 1)).space).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (X.level n).space (Y.level n).space).hom ≫
      pointedStep X (KanSequence.mapping A Y) n := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space),
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv A (X.level n).space]
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
      (Y.level (n + 1)).space).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [step_exchange X Y A n]
  rw [Iso.inv_hom_id_assoc]

/-- 転置した同じ実区間の構造像は、構造像の実区間の転置に厳密に一致。 -/
lemma basedTranspose_step_path (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A : PointedSimplicialSet.{u}} (n : ℕ)
    {f g : A ⟶ PointedObject.basedHom (X.level n).space (Y.level n).space}
    (H : PointedMapping.VerticalPath (PointedObject.toPoint _) f g) :
    (H.basedPost (pointedStep X Y n)).basedTranspose.path =
      (H.basedTranspose.suspension.forgetProjection.basedPost
        ((KanSequence.mapping A Y).sigma n)).path := by
  change (H.path ≫ ((ihom A).map (pointedStep X Y n)).right) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      (Y.level (n + 1)).space).hom.right =
    ((H.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (X.level n).space
      (Y.level n).space).hom.right) ≫
      (suspensionHom (X.level n).space ((KanSequence.mapping A Y).level n).space).right) ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mapping A Y).sigma n)).right
  simpa only [Under.comp_right, pointedStep, Category.assoc] using
    congrArg (fun k => H.path ≫ k.right) (step_exchange_transpose X Y A n)

/-- 源の構造射への制限も、同じ実区間の転置と厳密に可換。 -/
lemma basedTranspose_restriction_path {A U T V : PointedSimplicialSet.{u}}
    (i : T ⟶ U) {f g : A ⟶ PointedObject.basedHom U V}
    (H : PointedMapping.VerticalPath (PointedObject.toPoint _) f g) :
    (H.basedPost (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V)).basedTranspose.path =
      (H.basedTranspose.pre i).path := by
  change (H.path ≫ ((ihom A).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V)).right) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A T V).hom.right =
    (H.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom A V)).right
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right A i V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    PointedObject.ihom_obj_eq_basedHom] at h
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun k => H.path ≫ k.right) h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
