module

public import SerrePositivity.KST.Spectra.CotensorRestriction

/-!
概要：内部 Hom の標的の射を BF cotensor 間の実際の射へ持ち上げる。
方針：各段の後合成を単射置換の比較射へ厳密に持ち上げる。
規約：選んだ持ち上げの厳密な関手法則は要求しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理化の模型の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：スペクトルの射の後合成を cotensor の実際の BF 射にする。
方針：cofibrant な始域から標的の射影へ列として持ち上げる。
規約：内部 Hom の源 A は任意。
使われ方：BF 1978 §2、HTT A.3.3。loop 模型の実際の比較射。 -/
def cotensorPost (A : PointedSimplicialSet.{u}) {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    cotensor A X ⟶ cotensor A Y := by
  let g := KanSequence.liftHom (X := (cotensor A X).toKanSequence)
    (W := (cotensor A Y).toKanSequence) (Z := KanSequence.mapping A Y.toKanSequence)
    (cotensor A X).sigma_mono (cotensorProjection A Y) (cotensorProjection_rlp A Y)
    ((cotensorProjection A X).comp (KanSequence.mappingPost A ⟨f.app, f.comm⟩))
  exact { app := g.app, comm := g.comm }

/-- 概要：cotensor の後合成を元の内部 Hom へ戻すと通常の後合成。
方針：列の持ち上げの因子分解式を使う。
規約：各段で点つき射の厳密な等式。
使われ方：BF 1978 §2、HA §1.4.2。有理化図式と模型の比較。 -/
theorem cotensorPost_comparison (A : PointedSimplicialSet.{u})
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (cotensorPost A f).app n ≫ (cotensorProjection A Y).app n =
      (cotensorProjection A X).app n ≫ PointedObject.basedHomMap A (f.app n) :=
  KanSequence.liftHom_fac (X := (cotensor A X).toKanSequence)
    (W := (cotensor A Y).toKanSequence) (Z := KanSequence.mapping A Y.toKanSequence)
    (cotensor A X).sigma_mono (cotensorProjection A Y) (cotensorProjection_rlp A Y)
    ((cotensorProjection A X).comp (KanSequence.mappingPost A ⟨f.app, f.comm⟩)) n

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
