module

public import SerrePositivity.KST.Spectra.PointedSpectrumIntervalTranspose
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed

/-!
概要：元の全 Hom の実区間は、同じ区間全体で隣接段の構造条件を厳密に満たす。
方針：全 Hom の元の評価条件に内部 Hom を作用させ、同じ区間の辺へ後合成する。
規約：段ごとの成分類から推論しない。使われ方：源単位区間の実構造正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {T : PointedSimplicialSet.{u}}
  {f g : T ⟶ pointedSpace X Y}
  (P : PointedMapping.VerticalPath (PointedObject.toPoint (pointedSpace X Y)) f g)

/-- 元の同じ全 Hom 区間を二つの構造経路へ評価すると、区間全体が厳密に一致する。 -/
lemma pointedInterval_evaluation_condition (n : ℕ) :
    ((P.basedPost (pointedEvaluation X Y (n + 1))).basedPost
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space)).path =
    ((P.basedPost (pointedEvaluation X Y n)).basedPost (pointedStep X Y n)).path := by
  have he := congrArg ((ihom T).map) (pointedEvaluation_condition X Y n)
  simp only [Functor.map_comp] at he
  have hr := congrArg Under.Hom.right he
  change (P.path ≫ ((ihom T).map (pointedEvaluation X Y (n + 1))).right) ≫
      ((ihom T).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space)).right =
    (P.path ≫ ((ihom T).map (pointedEvaluation X Y n)).right) ≫
      ((ihom T).map (pointedStep X Y n)).right
  simpa only [Under.comp_right, Category.assoc] using congrArg (P.path ≫ ·) hr

/-- 同じ構造条件は、転置した段区間の源制限と列の構造像の厳密一致を与える。 -/
lemma pointedInterval_transposed_condition (n : ℕ) :
    (((P.basedPost (pointedEvaluation X Y (n + 1))).basedTranspose).pre (X.sigma n)).path =
    (PointedMapping.VerticalPath.basedPost
      (P.basedPost (pointedEvaluation X Y n)).basedTranspose.suspension.forgetProjection
      ((KanSequence.mapping T Y).sigma n)).path := by
  rw [← basedTranspose_restriction_path, ← basedTranspose_step_path]
  have h := pointedInterval_evaluation_condition X Y P n
  have ht := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso T (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (Y.level (n + 1)).space).hom.right) h
  exact ht

end SerrePositivity.KST.Spectra.RawSpectrumMapping
