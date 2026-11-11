module

public import SerrePositivity.KST.Spectra.SequenceParameterRelativeHomotopy
public import SerrePositivity.KST.Spectra.PointedTransposeIntervalRestriction

/-!
概要：相対厳密化で保持した修正鎖を、元の座標から最終座標への境界固定区間として回収する。
方針：同じ制限 fiber の順方向区間へ圧縮し、転置後の区間の制限を厳密に計算する。
規約：全列のホモトピーは主張しない。使われ方：非零境界の比較区間の相対合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A B : PointedSimplicialSet.{u}}
  (j : B ⟶ A) [Mono j.right] (c : B ⟶ pointedSpace X Y)
  (f : ∀ n, (X.level n).space ⟶ (ihom A).obj (Y.level n).space)
  (hb : ∀ n, f n ≫ (KanSequence.mappingPre j Y).app n =
    (homOfParameterFamily X Y B c).app n)
  (hf : ∀ n, PointedMapping.VerticalChain ((KanSequence.mappingPre j Y).app (n + 1))
    (X.sigma n ≫ f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ f n ≫ (KanSequence.mapping A Y).sigma n))

/-- 元の段座標から最終座標へ進み、指定非零境界の座標全体を固定する実区間。 -/
def relativeParameterForwardInterval (n : ℕ) :
    { P : PointedMapping.VerticalPath
        (PointedObject.toPoint (PointedObject.basedHom (X.level n).space (Y.level n).space))
        (PointedMapping.transpose (f n))
        (rectifyParameterRelative X Y j c f hb hf ≫ pointedEvaluation X Y n) //
      P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j
        (PointedObject.basedHom (X.level n).space (Y.level n).space)).right =
          SSet.const (PointedMapping.familyVertex (c ≫ pointedEvaluation X Y n)) } := by
  let P := Classical.choice ((relativeParameterHom_chain X Y j c f hb hf n).nonempty_path
    (mappingPre_level_horn_rlp j Y n))
  let Q := P.forgetProjection.basedTranspose
  let R := Q.changeEndpoints rfl (rectifyParameterRelative_evaluation X Y j c f hb hf n)
  have hB : j ≫ PointedMapping.transpose (f n) = c ≫ pointedEvaluation X Y n :=
    (PointedMapping.transpose_pre_inner (f n) j).symm.trans
      ((congrArg PointedMapping.transpose (hb n)).trans
        (homOfParameterFamily_transpose_evaluation X Y B c n))
  have h := PointedMapping.VerticalPath.transpose_path_restriction
    (j := j) (V := (Y.level n).space) P
  rw [hB] at h
  exact ⟨R, h⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
