module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PullbackPiComparison
public import SerrePositivity.KST.Spectra.Limits.SpectrumPullbackAdjoints

/-!
概要：段ごとの一脚 Kan fibration の引き戻し列の Ω 条件。
方針：実際の随伴比較射に引き戻しの全次数比較を適用し、単射性とともに束ねる。
規約：L9 の元の段ごとの引き戻しを使い、構造射の置換は行わない。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の引き戻し対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：Ω 条件を持つ三列の一脚 fibration の実際の引き戻し比較射は全基点 π_* 同型。
方針：各段の二つの引き戻しの fiber を同定し、全空間と底の全次数比較を適用する。
規約：零次数と空の fiber の検査を含め、元の三つの Ω 条件だけを使う。
使われ方：Sp の引き戻し列の随伴構造射の Ω 条件の検証。 -/
lemma pullbackAdjointMap_piIsomorphism {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    [∀ n, Fibration (f.app n).right]
    (hE : E.OmegaCondition) (hX : X.OmegaCondition) (hB : B.OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pullbackAdjointMap f g n).right := by
  let aE := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (E.sigma n)
  let aX := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n)
  let aB := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (B.sigma n)
  let pf := PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (n + 1))
  let pg := PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (g.app (n + 1))
  have hi : pullback.fst (f.app n) (g.app n) ≫ aE =
      pullbackAdjointMap f g n ≫ pullback.fst pf pg := by
    rw [pullbackAdjointMap, pullback.lift_fst]
  have hj : pullback.snd (f.app n) (g.app n) ≫ aX =
      pullbackAdjointMap f g n ≫ pullback.snd pf pg := by
    rw [pullbackAdjointMap, pullback.lift_snd]
  have hp : f.app n ≫ aB = aE ≫ pf := f.adjoint_comm n
  have hq : g.app n ≫ aB = aX ≫ pg := g.adjoint_comm n
  have hi' := congrArg Under.Hom.right hi
  have hj' := congrArg Under.Hom.right hj
  have hp' := congrArg Under.Hom.right hp
  have hq' := congrArg Under.Hom.right hq
  simp only [Under.comp_right] at hi' hj' hp' hq'
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackComparison_piIsomorphism
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (f.app n) (g.app n)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback pf pg)
    (pullbackAdjointMap f g n).right aE.right aX.right aB.right hi' hj' hp' hq'
    (hE n) (hX n) (hB n) (E.level n).space.basepoint

/-- 概要：三列の Ω 条件は一脚が段ごとに fibration の引き戻し列へ保存される。
方針：実際の比較射の全基点 π_* 同型を随伴比較の同値へ渡す。
規約：全自然数次数を扱い、構造射の単射性はこの条件の証明には不要。
使われ方：BF 1978 §2、Sp の段ごとの引き戻しの Ω 条件。 -/
lemma pullbackSequence_omega {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    [∀ n, Fibration (f.app n).right]
    (hE : E.OmegaCondition) (hX : X.OmegaCondition) (hB : B.OmegaCondition) :
    (KanSequence.pullbackSequence f g).OmegaCondition :=
  (pullbackSequence_omega_iff f g).mpr (pullbackAdjointMap_piIsomorphism f g hE hX hB)

/-- 概要：L9 の Ω スペクトルの一脚が段ごとに fibration の実際の引き戻し対象。
方針：元の段ごとの引き戻し列の単射な構造射と Ω 条件を検証して束ねる。
規約：各段を置換せず点つき通常引き戻しそのものに取る。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の引き戻し錐の頂点。 -/
def spectrumPullback {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : OmegaSpectrum.{u} :=
  let fs : KanSequence.Hom E.toKanSequence B.toKanSequence := ⟨f.app, f.comm⟩
  let gs : KanSequence.Hom X.toKanSequence B.toKanSequence := ⟨g.app, g.comm⟩
  (KanSequence.pullbackSequence fs gs).toOmegaSpectrum
    (pullbackSigma_mono fs gs E.sigma_mono X.sigma_mono)
    (pullbackSequence_omega fs gs E.toKanSequence_omega X.toKanSequence_omega
      B.toKanSequence_omega)

/-- 概要：引き戻しスペクトルから第一のスペクトルへの厳密な射影。
方針：各段の第一射影と構造射の計算式を使う。
規約：元の Ω スペクトルの射として与える。
使われ方：Sp の引き戻し錐の第一の脚。 -/
def spectrumPullbackFst {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : spectrumPullback f g ⟶ E where
  app n := pullback.fst (f.app n) (g.app n)
  comm n := by
    change _ = KanSequence.pullbackSigma _ _ n ≫ pullback.fst _ _
    simp only [KanSequence.pullbackSigma, pullback.lift_fst]
    rfl

/-- 概要：引き戻しスペクトルから第二のスペクトルへの厳密な射影。
方針：各段の第二射影と構造射の計算式を使う。
規約：元の Ω スペクトルの射として与える。
使われ方：Sp の引き戻し錐の第二の脚。 -/
def spectrumPullbackSnd {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : spectrumPullback f g ⟶ X where
  app n := pullback.snd (f.app n) (g.app n)
  comm n := by
    change _ = KanSequence.pullbackSigma _ _ n ≫ pullback.snd _ _
    simp only [KanSequence.pullbackSigma, pullback.lift_snd]
    rfl

/-- 概要：引き戻しの二つの射影の元の底への合成は等しい。
方針：各段で通常の引き戻しの可換条件を適用する。
規約：スペクトルの射として厳密な等式。
使われ方：Sp の実際の引き戻し錐の可換条件。 -/
lemma spectrumPullback_condition {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] :
    spectrumPullbackFst f g ≫ f = spectrumPullbackSnd f g ≫ g :=
  OmegaSpectrum.Hom.ext (fun _ ↦ pullback.condition)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
