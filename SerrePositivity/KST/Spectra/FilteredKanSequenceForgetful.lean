module

public import SerrePositivity.KST.Spectra.FilteredKanSequence
public import SerrePositivity.KST.Spectra.KanSequenceForgetful

/-!
概要：BF 図式の Kan 列への忘却は filtered 余極限構成を保つ。
方針：同じ段の図式と構造射の定義を比較する。
規約：置換を二度行わず、既存の telescope をそのまま利用する。
使われ方：BF 1978 §2、HA §1.4.2。有理化の自然性の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 概要：忘却後の Kan 余極限列は既存の BF 図式の余極限列と一致する。
方針：各段と構造射の定義を展開する。
規約：Kan 列の等式。
使われ方：BF 1978 §2。既存の telescope への比較。 -/
theorem filteredKanSequence_forget (D : J ⥤ OmegaSpectrum.{u}) :
    KanSequence.filteredKanSequence (D ⋙ forgetToKan) = filteredKanSequence D := rfl

/-- 概要：忘却後の BF 余極限対象は既存の対象と一致する。
方針：同じ Kan 列の同じ単射置換を使う。
規約：Ω 条件の証明は proof irrelevance で一致する。
使われ方：BF 1978 §2、HA §1.4.2。有理化の対象を保つ。 -/
theorem filteredOmegaSpectrum_forget (D : J ⥤ OmegaSpectrum.{u}) :
    KanSequence.filteredOmegaSpectrum (D ⋙ forgetToKan)
      (fun j ↦ (D.obj j).toKanSequence_omega) = filteredOmegaSpectrum D := rfl

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
