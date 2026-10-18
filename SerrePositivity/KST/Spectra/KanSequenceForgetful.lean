module

public import SerrePositivity.KST.Spectra.KanSequenceCategory
public import SerrePositivity.KST.Spectra.FilteredOmegaSpectrum

/-!
概要：BF 対象から厳密な Kan 列の圏への忘却関手。
方針：各段と構造射および厳密な射を変えずに単射性と Ω 条件を忘れる。
規約：段の評価関手との等式を実際の関手の等式で記す。
使われ方：BF 1978 §2、HA §1.4.2。既存の BF telescope と置換前の Kan 列の図式の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 概要：BF 対象と厳密な射を単射置換前の Kan 列の圏へ送る。
方針：各段と構造可換式をそのまま使う。
規約：通常の圏の関手として恒等・合成を保つ。
使われ方：BF 1978 §2。telescope の比較の自然変換の始域の図式。 -/
def forgetToKan : OmegaSpectrum.{u} ⥤ KanSequence.{u} where
  obj := toKanSequence
  map f := ⟨f.app, f.comm⟩
  map_id _ := by apply KanSequence.Hom.ext_app; intro n; rfl
  map_comp _ _ := by apply KanSequence.Hom.ext_app; intro n; rfl

/-- 概要：BF 対象の段評価は忘却後の Kan 列の段評価と一致する。
方針：対象と射の各段の表示を比較する。
規約：自然同型だけでなく関手の等式。
使われ方：HA §1.4.2。既存の telescope の段ごとの余極限を保つ。 -/
theorem forgetToKan_levelEvaluation (n : ℕ) :
    forgetToKan.{u} ⋙ KanSequence.levelEvaluation n = levelEvaluation n := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
