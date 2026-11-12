module

public import SerrePositivity.KST.Spectra.SequenceRelativeTracedTriangles
public import SerrePositivity.KST.Spectra.SequenceParameterRelativeRectification
public import SerrePositivity.KST.Spectra.PointedRelativeTransposeHomotopy
public import SerrePositivity.KST.Spectra.PointedTransposeIntervalRestriction

/-!
概要：実垂直区間と構造三角形を保持する相対列厳密化を、元の全パラメータ族へ戻す。
方針：内部 Hom の制限を射影に使い、段射と実区間の同じ転置で全体の族を回収する。
規約：指定非零境界と実構造三角形を保持。使われ方：全列の比較の高次整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A B : PointedSimplicialSet.{u}}
  (j : B ⟶ A) [Mono j.right] (c : B ⟶ pointedSpace X Y)
  (f : ∀ n, (X.level n).space ⟶ (ihom A).obj (Y.level n).space)
  (hb : ∀ n, f n ≫ (KanSequence.mappingPre j Y).app n =
    (homOfParameterFamily X Y B c).app n)
  (h : ∀ n, PointedMapping.VerticalPath ((KanSequence.mappingPre j Y).app (n + 1))
    (X.sigma n ≫ f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ f n ≫ (KanSequence.mapping A Y).sigma n))

/-- 指定境界の上で、元の実区間・三角形を保持して厳密化した cotensor 値の列射。 -/
def relativeTracedParameterHom : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y) :=
  KanSequence.relativeTracedRectify X.sigma_mono (KanSequence.mappingPre j Y)
    (mappingPre_level_horn_rlp j Y) (homOfParameterFamily X Y B c) f hb h

/-- 保存した相対列射を、元の全パラメータ族として回収する。 -/
def rectifyParameterRelativeTraced : A ⟶ pointedSpace X Y :=
  parameterFamily X Y A (relativeTracedParameterHom X Y j c f hb h)

/-- 元の指定境界への射影は全段で厳密に保持する。 -/
lemma relativeTracedParameterHom_projection (n : ℕ) :
    (relativeTracedParameterHom X Y j c f hb h).app n ≫ (KanSequence.mappingPre j Y).app n =
      (homOfParameterFamily X Y B c).app n :=
  KanSequence.relativeTracedRectify_projection X.sigma_mono (KanSequence.mappingPre j Y)
    (mappingPre_level_horn_rlp j Y) (homOfParameterFamily X Y B c) f hb h n

/-- 修正後の段座標は、同じ修正済み段射の転置。 -/
lemma rectifyParameterRelativeTraced_evaluation (n : ℕ) :
    rectifyParameterRelativeTraced X Y j c f hb h ≫ pointedEvaluation X Y n =
      PointedMapping.transpose ((relativeTracedParameterHom X Y j c f hb h).app n) :=
  parameterFamily_evaluation X Y A (relativeTracedParameterHom X Y j c f hb h) n

/-- 元の指定された非零境界は、全列の族として厳密に保持される。 -/
lemma rectifyParameterRelativeTraced_boundary :
    j ≫ rectifyParameterRelativeTraced X Y j c f hb h = c := by
  apply pointed_hom_ext X Y
  intro n
  rw [Category.assoc, rectifyParameterRelativeTraced_evaluation]
  have hp := relativeTracedParameterHom_projection X Y j c f hb h n
  exact (PointedMapping.transpose_pre_inner
    ((relativeTracedParameterHom X Y j c f hb h).app n) j).symm.trans
      ((congrArg PointedMapping.transpose hp).trans
        (homOfParameterFamily_transpose_evaluation X Y B c n))

/-- 元の段射からの同じ実垂直比較区間を回収する。 -/
def relativeTracedParameterComparison (n : ℕ) :
    PointedMapping.VerticalPath ((KanSequence.mappingPre j Y).app n) (f n)
      ((relativeTracedParameterHom X Y j c f hb h).app n) :=
  KanSequence.relativeTracedRectifyComparison X.sigma_mono (KanSequence.mappingPre j Y)
    (mappingPre_level_horn_rlp j Y) (homOfParameterFamily X Y B c) f hb h n

/-- 同じ垂直比較を転置して、元の非零境界を固定する段座標区間へ戻す。 -/
def relativeTracedParameterEvaluationInterval (n : ℕ) :
    { P : PointedMapping.VerticalPath
        (PointedObject.toPoint (PointedObject.basedHom (X.level n).space (Y.level n).space))
        (PointedMapping.transpose (f n))
        (rectifyParameterRelativeTraced X Y j c f hb h ≫ pointedEvaluation X Y n) //
      P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j
        (PointedObject.basedHom (X.level n).space (Y.level n).space)).right =
          SSet.const (PointedMapping.familyVertex (c ≫ pointedEvaluation X Y n)) } := by
  let P := relativeTracedParameterComparison X Y j c f hb h n
  let Q := P.forgetProjection.basedTranspose
  let R := Q.changeEndpoints rfl (rectifyParameterRelativeTraced_evaluation X Y j c f hb h n)
  have hB : j ≫ PointedMapping.transpose (f n) = c ≫ pointedEvaluation X Y n :=
    (PointedMapping.transpose_pre_inner (f n) j).symm.trans
      ((congrArg PointedMapping.transpose (hb n)).trans
        (homOfParameterFamily_transpose_evaluation X Y B c n))
  have hp := PointedMapping.VerticalPath.transpose_path_restriction
    (j := j) (V := (Y.level n).space) P
  rw [hB] at hp
  exact ⟨R, hp⟩

/-- 相対段評価区間を再び転置すると、元の同じ実垂直区間の族へ戻る。 -/
lemma relativeTracedParameterEvaluationInterval_transpose_path (n : ℕ) :
    (relativeTracedParameterEvaluationInterval X Y j c f hb h n).val.basedTranspose.path =
      (relativeTracedParameterComparison X Y j c f hb h n).path := by
  let P := relativeTracedParameterComparison X Y j c f hb h n
  let Q := P.forgetProjection.basedTranspose
  have he : (relativeTracedParameterEvaluationInterval X Y j c f hb h n).val.basedTranspose.path =
      Q.basedTranspose.path :=
    PointedMapping.VerticalPath.changeEndpoints_basedTranspose_path Q rfl
      (rectifyParameterRelativeTraced_evaluation X Y j c f hb h n)
  exact he.trans P.forgetProjection.basedTranspose_twice_path

end SerrePositivity.KST.Spectra.RawSpectrumMapping
