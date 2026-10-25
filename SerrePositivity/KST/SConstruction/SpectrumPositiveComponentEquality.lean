module
public import SerrePositivity.KST.SConstruction.SpectrumIntegerComponentEquality

/-!
概要：正段の基点固定比較だけで、BF 射の全整数次数の作用を一致させる。
方針：整数次数の標準表示が常に正段にあることを使う。
規約：零段の比較や全スペクトル写像空間の比較を要求しない。
使われ方：有限 native BF 四角形の新しい四辺と旧 K 射の整数群比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra Spectra.PointedMapping

/-- 概要：正段で同じ基点固定成分を持つ BF 射は、全整数群で同じ作用を持つ。
方針：次数 j の標準段 j.natAbs + 1 で比較する。
規約：同じ始域と終域を固定する。使われ方：有限四辺の整数 π 作用の回収。 -/
lemma spectrumHomotopyMap_eq_of_positive_component {X Y : OmegaSpectrum.{u}}
    (f g : X ⟶ Y) (h : ∀ r, componentOf (f.app (r + 1)) =
      componentOf (g.app (r + 1))) (j : ℤ) :
    OmegaSpectrum.homotopyMap f j = OmegaSpectrum.homotopyMap g j := by
  apply MonoidHom.ext
  intro a
  rw [OmegaSpectrum.homotopyMap_apply, OmegaSpectrum.homotopyMap_apply]
  exact congrFun (pointedHomotopyMap_eq_of_component (h j.natAbs)
    (OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j))) a

end SerrePositivity.KST.SConstruction
