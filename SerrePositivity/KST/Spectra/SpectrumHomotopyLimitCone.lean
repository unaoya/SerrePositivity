module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitCone
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting

/-!
概要：BF 図式の厳密な錐から段ごとの homotopy end の BF 対象への標準比較射。
方針：Kan 列への実際の錐の比較を、cofibrant な源から標準置換の射影へ持ち上げる。
規約：∞ 極限性や極限錐の仮定を要求しない。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。自明作用から hG への標準射。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {D : I ⥤ OmegaSpectrum.{u}}

/-- 概要：段ごとの BF homotopy end から置換前の Kan 列への標準射影。
方針：Kan Ω 列の cofibrant 置換の標準射を使う。
規約：Ω 条件は元の各 BF 対象から得る。
使われ方：HA §1.4.2、BF 1978 §2。標準比較射の各段の計算。 -/
def homotopyLimitProjection (D : I ⥤ OmegaSpectrum.{u}) :
    KanSequence.Hom (homotopyLimit D).toKanSequence (KanSequence.homotopyLimit (D ⋙ forgetToKan)) :=
  KanSequence.homotopyLimitProjection (D ⋙ forgetToKan) (fun i ↦ (D.obj i).toKanSequence_omega)

/-- 概要：厳密な BF 錐から homotopy end の BF 対象への実際の射。
方針：Kan 列の標準比較を標的の単射置換へ持ち上げる。
規約：持ち上げの選択を固定し、極限性は仮定しない。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。自明作用の hG への実際の比較。 -/
def homotopyLimitConeComparison (c : Cone D) : c.pt ⟶ homotopyLimit D := by
  let f := KanSequence.liftHom (X := c.pt.toKanSequence)
    (W := (homotopyLimit D).toKanSequence) (Z := KanSequence.homotopyLimit (D ⋙ forgetToKan))
    c.pt.sigma_mono (homotopyLimitProjection D)
    (fun n ↦ (KanSequence.replacementStage (KanSequence.homotopyLimit (D ⋙ forgetToKan)) n).projection_rlp)
    (KanSequence.homotopyLimitCone (forgetToKan.mapCone c))
  exact { app := f.app, comm := f.comm }

/-- 概要：BF 標準比較を置換前へ射影すると段ごとの定数族の比較になる。
方針：列の持ち上げの因子分解式を取り出す。
規約：各段の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。標準射の π_* を Kan end の計算へ戻す。 -/
theorem homotopyLimitConeComparison_projection (c : Cone D) (n : ℕ) :
    (homotopyLimitConeComparison c).app n ≫ (homotopyLimitProjection D).app n =
      KanSequence.homotopyLimitConeApp (forgetToKan.mapCone c) n :=
  KanSequence.liftHom_fac (X := c.pt.toKanSequence)
    (W := (homotopyLimit D).toKanSequence) (Z := KanSequence.homotopyLimit (D ⋙ forgetToKan))
    c.pt.sigma_mono (homotopyLimitProjection D)
    (fun k ↦ (KanSequence.replacementStage (KanSequence.homotopyLimit (D ⋙ forgetToKan)) k).projection_rlp)
    (KanSequence.homotopyLimitCone (forgetToKan.mapCone c)) n

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
