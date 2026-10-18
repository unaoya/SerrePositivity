module

public import SerrePositivity.KST.Spectra.FixedPointSpectra
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitCone

/-!
概要：自明な群作用を持つ元のスペクトルから hG への実際の標準比較。
方針：自明作用の厳密な定数錐を作り、Kan end の比較を BF 置換へ持ち上げる。
規約：この定義だけから比較が π_* 同型であるとは主張しない。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。有理 Shapiro の実際の比較射。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自明な群作用の図式には元の対象を頂点とする厳密な錐がある。
方針：各成分を恒等射とし、自明作用の全ての射も恒等射であることを使う。
規約：群の有限性は不要。
使われ方：HA §1.4.2。hG への標準比較の始域を指定する錐。 -/
def trivialActionCone (G : Type u) [Group G] (X : OmegaSpectrum.{u}) :
    Cone (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj (Action.trivial G X)) where
  pt := X
  π := {
    app _ := 𝟙 X
    naturality _ _ _ := by
      change 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ 𝟙 X
      rfl }

/-- 概要：自明作用を持つ元の対象から homotopy fixed points への実際の BF 射。
方針：厳密な定数錐から点つき Kan end への比較を cofibrant な源から持ち上げる。
規約：群の有限性や有理性を構成そのものには要求しない。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。有理自明作用の Shapiro の比較射。 -/
def homotopyFixedPointsUnit (G : Type u) [Group G] (X : OmegaSpectrum.{u}) :
    X ⟶ homotopyFixedPoints (Action.trivial G X) :=
  OmegaSpectrum.homotopyLimitConeComparison (trivialActionCone G X)

/-- 概要：自明作用の hG への標準射を置換前へ戻すと定数族の end 比較になる。
方針：BF 錐の比較の射影式を自明作用の定数錐へ適用する。
規約：各段の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。有理 Shapiro の π_* 同型の計算の出発点。 -/
theorem homotopyFixedPointsUnit_projection (G : Type u) [Group G] (X : OmegaSpectrum.{u}) (n : ℕ) :
    (homotopyFixedPointsUnit G X).app n ≫
      (homotopyFixedPointsProjection (Action.trivial G X)).app n =
    KanSequence.homotopyLimitConeApp
      (OmegaSpectrum.forgetToKan.mapCone (trivialActionCone G X)) n :=
  OmegaSpectrum.homotopyLimitConeComparison_projection (trivialActionCone G X) n

end

end SerrePositivity.KST.Spectra
