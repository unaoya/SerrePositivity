module

public import SerrePositivity.KST.Spectra.EndpointLoopToPathSpectrum
public import SerrePositivity.KST.Spectra.BasedLoopSquare

/-!
概要：二端点を潰した円の BF cotensor から、native loop の具体的な BF 引き戻しへの射。
方針：BF path への制限と一点への零射を、その厳密な零合成で引き戻しへ持ち上げる。
規約：比較射は実際の BF 射。使われ方：loop cotensor と native loop 四角形の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits

namespace SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop

/-- BF loop から具体的な native loop 対象への実際の比較。 -/
def comparison (Y : OmegaSpectrum.{u}) : cotensor endpointCircle Y ⟶ obj Y := by
  let L := cotensor endpointCircle Y
  let a := endpointLoopToPath Y
  let b : L ⟶ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint := 0
  have h : a ≫ basedPathProjection Y = b ≫ fromPoint Y := by
    rw [endpointLoopToPath_projection_zero]
    exact (zero_comp (f := fromPoint Y)).symm
  let f : KanSequence.Hom (basedPath Y).toKanSequence Y.toKanSequence :=
    ⟨(basedPathProjection Y).app, (basedPathProjection Y).comm⟩
  let g : KanSequence.Hom _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence Y.toKanSequence :=
    ⟨(fromPoint Y).app, (fromPoint Y).comm⟩
  let q := KanSequence.pullbackLift f g
    (⟨a.app, a.comm⟩ : KanSequence.Hom L.toKanSequence (basedPath Y).toKanSequence)
    (⟨b.app, b.comm⟩ : KanSequence.Hom L.toKanSequence _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence)
    (fun n ↦ congrArg (fun t : L ⟶ Y ↦ t.app n) h)
  exact ⟨q.app, q.comm⟩

/-- 第一射影との合成は元の BF path への制限。 -/
@[reassoc (attr := simp)]
lemma comparison_fst (Y : OmegaSpectrum.{u}) :
    comparison Y ≫ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackFst (basedPathProjection Y) (fromPoint Y) =
      endpointLoopToPath Y :=
  OmegaSpectrum.Hom.ext (fun _ ↦ pullback.lift_fst _ _ _)

/-- 第二射影との合成は一点への零射。 -/
@[reassoc (attr := simp)]
lemma comparison_snd (Y : OmegaSpectrum.{u}) :
    comparison Y ≫ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackSnd (basedPathProjection Y) (fromPoint Y) = 0 :=
  OmegaSpectrum.Hom.ext (fun _ ↦ pullback.lift_snd _ _ _)

end SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
