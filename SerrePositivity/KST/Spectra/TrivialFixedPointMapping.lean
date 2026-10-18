module

public import SerrePositivity.KST.Spectra.ConstantPointedHomotopyEnd
public import SerrePositivity.KST.Spectra.FixedPointSpectra

/-!
概要：自明作用の homotopy fixed points の各段の nerve からの写像空間表示。
方針：自明作用の段ごとの定値係数図式へ点つき homotopy end の同型を適用する。
規約：cofibrant 置換前の Kan end を同定する。群の有限性と有理性は不要。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の各段の模型。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自明作用の置換前の hG の段は BG から係数段への写像空間。
方針：作用の図式が厳密に定値であることと点つき end の比較を使う。
規約：BG は宇宙をそろえた一対象群圏の nerve。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の骨格の塔の始点。 -/
def trivialFixedPointLevelIso (G : Type u) [Group G] (X : OmegaSpectrum.{u}) (k : ℕ) :
    ((homotopyFixedPointsKan (Action.trivial G X)).level k).space ≅
      UnbasedPointedMapping.obj (nerve (AsSmall.{u} (SingleObj G))) (X.level k).space :=
  constantPointedHomotopyEndIso (AsSmall.{u} (SingleObj G)) (X.level k).space

end

end SerrePositivity.KST.Spectra
