module

public import SerrePositivity.KST.Spectra.FilteredSpectrumInjection

/-!
概要：非連結化に用いる逐次 BF 模型と、その整数 π の余極限。
方針：Sp レーンの filtered 構成を同じ宇宙の自然数列に特殊化する。
規約：実 Sp cocone は SequentialCoherentCocone で構成する。∞ 余極限性は別工程。
使われ方：K-7 工程 1。後続の dg 懸垂列を受け取る対象側の界面。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.NonConnective

noncomputable section

/-- 概要：BF 値と同じ宇宙に持ち上げた逐次添字。
方針：自然数の順序圏を使う。
規約：対象宇宙を縮めない。
使われ方：K-7 の反復懸垂列。 -/
abbrev SequentialIndex := ULift.{u} ℕ

/-- 概要：非連結化の入力となる厳密な BF スペクトル列。
方針：順序圏からの通常の関手を使う。
規約：任意の coherent 列の整流は仮定しない。
使われ方：K-7 の対象の構成。 -/
abbrev SpectrumSequence := SequentialIndex.{u} ⥤ OmegaSpectrum.{u}

/-- 概要：逐次列の段ごとの Kan 余極限を BF 置換した候補。
方針：Sp の既存 filteredOmegaSpectrum をそのまま使う。
規約：∞ 余極限の普遍性を定義に含めない。
使われ方：後続の非連結 K の対象候補。 -/
abbrev sequentialSpectrum (D : SpectrumSequence.{u}) : OmegaSpectrum.{u} :=
  OmegaSpectrum.filteredOmegaSpectrum D

/-- 概要：元の各段から BF 候補への選択済みの厳密射。
方針：Sp の既存持ち上げを使う。
規約：BF 射としての厳密自然性は主張しない。
使われ方：比較射と整数 π の計算。 -/
abbrev sequentialInjection (D : SpectrumSequence.{u}) (n : ℕ) :
    D.obj ⟨n⟩ ⟶ sequentialSpectrum D :=
  OmegaSpectrum.filteredSpectrumInjection D ⟨n⟩

/-- 概要：逐次 BF 候補の整数 π を頂点に持つ群 cocone。
方針：選択した注入の整数 π 上の自然性を使う。
規約：群 cocone であり Sp cocone ではない。
使われ方：連結 K との次数別比較。 -/
def sequentialPiCocone (D : SpectrumSequence.{u}) (j : ℤ) :
    Cocone (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) where
  pt := GrpCat.of (OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j)
  ι := {
    app n := GrpCat.ofHom (OmegaSpectrum.homotopyMap
      (OmegaSpectrum.filteredSpectrumInjection D n) j)
    naturality _ _ f := by
      exact congrArg GrpCat.ofHom
        (OmegaSpectrum.filteredSpectrumInjection_natural D j f) }

/-- 概要：上の同じ整数 π cocone は群の余極限。
方針：Sp の比較同型とその各注入の式で標準余極限から移す。
規約：全整数 j。Sp の ∞ 余極限性を使わない。
使われ方：候補の π の普遍性。 -/
def sequentialPiCoconeIsColimit (D : SpectrumSequence.{u}) (j : ℤ) :
    IsColimit (sequentialPiCocone D j) :=
  IsColimit.ofIsoColimit
    (colimit.isColimit (OmegaSpectrum.spectrumHomotopyGroupDiagram D j))
    (Cocone.ext (OmegaSpectrum.filteredSpectrumHomotopyIso D j)
      (fun n ↦ OmegaSpectrum.filteredSpectrumHomotopyIso_ι D j n))

/-- 概要：同じ π cocone の台集合も余極限。
方針：群から集合への忘却が filtered 余極限を保存することを使う。
規約：元の群への注入を保持する。
使われ方：元の段での表示と等号判定。 -/
def sequentialPiUnderlyingIsColimit (D : SpectrumSequence.{u}) (j : ℤ) :
    IsColimit ((forget GrpCat).mapCocone (sequentialPiCocone D j)) :=
  isColimitOfPreserves (forget GrpCat) (sequentialPiCoconeIsColimit D j)

end

end SerrePositivity.KST.NonConnective
