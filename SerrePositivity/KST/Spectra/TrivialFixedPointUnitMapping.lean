module

public import SerrePositivity.KST.Spectra.ConstantPointedHomotopyCone
public import SerrePositivity.KST.Spectra.TrivialFixedPointMapping
public import SerrePositivity.KST.Spectra.FixedPointUnit

/-!
概要：自明作用の hG の標準射は各段で BG 上の定数写像となる。
方針：BF 射を置換前へ射影し、定値点つき homotopy end の比較へ移す。
規約：群の有限性も係数の有理性も要求しない厳密な等式。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の標準射の計算。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自明作用の hG への標準比較は置換前の写像空間で定数族。
方針：標準比較の射影式と定値図式の点つき比較式を合成する。
規約：各段の実際の点つき射の等式。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の π_* 同型の射を固定する。 -/
theorem homotopyFixedPointsUnit_mapping (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (k : ℕ) :
    (homotopyFixedPointsUnit G X).app k ≫
      (homotopyFixedPointsProjection (Action.trivial G X)).app k ≫
        (trivialFixedPointLevelIso G X k).hom =
      UnbasedPointedMapping.constant (nerve (AsSmall.{u} (SingleObj G))) (X.level k).space := by
  rw [← Category.assoc, homotopyFixedPointsUnit_projection]
  exact constantPointedHomotopyEndIso_unit (AsSmall.{u} (SingleObj G)) (X.level k).space

end

end SerrePositivity.KST.Spectra
