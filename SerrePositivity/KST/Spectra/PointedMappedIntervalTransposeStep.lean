module

public import SerrePositivity.KST.Spectra.PointedSpectrumIntervalTranspose
public import SerrePositivity.KST.Spectra.PointedIntervalNaturality

/-!
概要：パラメータ付き段区間の構造像を転置すると、同じ評価区間の構造像になる。
方針：元の mapping 列の構造交換を同じ実辺へ後合成する。
規約：区間の再選択なし。使われ方：源単位三角形の第二辺の構造座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- mapping 列に値を取る同じ段区間の構造像と転置は、辺全体で厳密に可換。 -/
lemma basedTranspose_mapped_step_path (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A : PointedSimplicialSet.{u}} (n : ℕ)
    {f g : (X.level n).space ⟶ PointedObject.basedHom A (Y.level n).space}
    (H : PointedMapping.VerticalPath (PointedObject.toPoint _) f g) :
    (H.suspension.forgetProjection.basedPost
      ((KanSequence.mapping A Y).sigma n)).basedTranspose.path =
    (H.basedTranspose.basedPost (pointedStep X Y n)).path := by
  change (H.path ≫ (pointedStep X (KanSequence.mapping A Y) n).right) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
        (Y.level (n + 1)).space).hom.right =
    (H.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).hom.right) ≫
      (PointedObject.basedHomMap A (pointedStep X Y n)).right
  have h := step_exchange X Y A n
  change pointedStep X (KanSequence.mapping A Y) n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
        (Y.level (n + 1)).space).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).hom ≫
      PointedObject.basedHomMap A (pointedStep X Y n) at h
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun k => H.path ≫ k.right) h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
