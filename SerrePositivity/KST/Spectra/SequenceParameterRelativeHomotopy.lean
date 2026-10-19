module

public import SerrePositivity.KST.Spectra.SequenceParameterRelativeRectification
public import SerrePositivity.KST.Spectra.PointedRelativeTransposeHomotopy

/-!
概要：相対厳密化の元の段座標を、指定部分全体を固定する単一のホモトピーで比較する。
方針：各段で保持した垂直有限鎖を元の Hom fiber 内で圧縮し、転置後に境界族へ照合する。
規約：段ごとの比較であり全列のホモトピーではない。使われ方：相対パラメータ族の類の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A B : PointedSimplicialSet.{u}}
  (j : B ⟶ A) [Mono j.right] (c : B ⟶ pointedSpace X Y)
  (f : ∀ n, (X.level n).space ⟶ (ihom A).obj (Y.level n).space)
  (hb : ∀ n, f n ≫ (KanSequence.mappingPre j Y).app n =
    (homOfParameterFamily X Y B c).app n)
  (hf : ∀ n, PointedMapping.VerticalChain ((KanSequence.mappingPre j Y).app (n + 1))
    (X.sigma n ≫ f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ f n ≫ (KanSequence.mapping A Y).sigma n))

/-- 元の段座標との比較は、基点と指定部分上の元の族を全区間で固定する。 -/
lemma rectifyParameterRelative_evaluation_relative_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (rectifyParameterRelative X Y j c f hb hf ≫
        pointedEvaluation X Y n).right (PointedMapping.transpose (f n)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (PointedObject.basedHom (X.level n).space (Y.level n).space).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        fst B.right (Δ[1] : SSet.{u}) ≫ (c ≫ pointedEvaluation X Y n).right := by
  rw [rectifyParameterRelative_evaluation]
  obtain ⟨H, hbase, hrel⟩ :=
    PointedMapping.VerticalChain.transpose_reverse_homotopy j
      (relativeParameterHom_chain X Y j c f hb hf n)
  have he : j ≫ PointedMapping.transpose ((relativeParameterHom X Y j c f hb hf).app n) =
      c ≫ pointedEvaluation X Y n := by
    rw [← rectifyParameterRelative_evaluation, ← Category.assoc,
      rectifyParameterRelative_boundary]
  have he' := congrArg Under.Hom.right he
  change j.right ≫
      (PointedMapping.transpose ((relativeParameterHom X Y j c f hb hf).app n)).right =
    (c ≫ pointedEvaluation X Y n).right at he'
  exact ⟨H, hbase, hrel.trans (congrArg (fst B.right (Δ[1] : SSet.{u}) ≫ ·) he')⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
