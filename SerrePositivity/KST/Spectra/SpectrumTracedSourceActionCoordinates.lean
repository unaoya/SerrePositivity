module

public import SerrePositivity.KST.Spectra.PointedIhomParameterExchange
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceActionInterval
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceEvaluationInterval

/-!
概要：全列作用で得た二つの元の族を、実評価とトレース付き源単位の元の段座標へ同定する。
方針：元のパラメータ族の段射を転置で表示し、内部 Hom の作用の厳密交換則を使う。
規約：全 Hom の射の等式。使われ方：全列区間を元の実評価のホモトピーへ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元のパラメータ族へ移した列射の各段は、同じ段評価の転置そのもの。 -/
lemma homOfParameterFamily_app (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (φ : A ⟶ pointedSpace X Y) (n : ℕ) :
    (homOfParameterFamily X Y A φ).app n =
      PointedMapping.transpose (φ ≫ pointedEvaluation X Y n) := by
  have h := congrArg PointedMapping.transpose
    (homOfParameterFamily_transpose_evaluation X Y A φ n)
  rw [PointedMapping.transpose_transpose] at h
  exact h

variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の列射へ全パラメータの符号付き loop 作用を後合成した族の厳密な段評価。 -/
lemma signedLoopActionFamily_evaluation
    (q : KanSequence.Hom X.toKanSequence (KanSequence.signedLoopTail X.toKanSequence)) (n : ℕ) :
    parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
        (q.comp (KanSequence.signedLoopParameterHom (homOfParameterFamily X Y.toKanSequence A φ))) ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n =
    (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1)) ≫
      PointedMapping.ihomAction CirclePower.space.{u}
        (X.level (n + 1)).space (Y.level (n + 1)).space ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (q.app n)
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space) := by
  rw [parameterFamily_evaluation]
  change PointedMapping.transpose (q.app n ≫
    (KanSequence.signedLoopParameterHom (homOfParameterFamily X Y.toKanSequence A φ)).app n) = _
  rw [KanSequence.signedLoopParameterHom_app, homOfParameterFamily_app]
  exact PointedMapping.transpose_ihomParameterAction
    (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1)) (q.app n)

/-- 全列区間の始点の族は、元の同じ入力に元の実評価を後合成した写像に厳密一致する。 -/
lemma tracedSourceActionParameterFamily (X Y : OmegaSpectrum.{u})
    {A : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence) :
    parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
        (tracedSourceActionParameterHom X Y φ) =
      φ ≫ OmegaSpectrum.CotensorCompatible.signedEvaluationAt X Y
        (OmegaSpectrum.tracedOriginalLoopModelMap X) := by
  apply pointed_hom_ext X (KanSequence.signedLoopTail Y.toKanSequence)
  intro n
  rw [tracedSourceActionParameterHom, signedLoopActionFamily_evaluation]
  simp only [Category.assoc]
  rw [OmegaSpectrum.CotensorCompatible.signedEvaluationAt_action]
  rfl

/-- 全列区間の終点を、元の Hom に値を取る源単位作用の実際の族として名前を付ける。 -/
def tracedSourceUnitFamily : A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
    (tracedUnitSourceActionParameterHom X Y φ)

/-- 終点族の各段も、既存の源単位作用の元の段座標そのもの。 -/
lemma tracedSourceUnitFamily_evaluation (n : ℕ) :
    tracedSourceUnitFamily X Y φ ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n =
    φ ≫ OmegaSpectrum.CotensorCompatible.tracedSourceUnitAction X Y n := by
  rw [tracedSourceUnitFamily, tracedUnitSourceActionParameterHom, signedLoopActionFamily_evaluation]
  simp only [OmegaSpectrum.CotensorCompatible.tracedSourceUnitAction, Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
