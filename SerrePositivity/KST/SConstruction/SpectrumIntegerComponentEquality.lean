module
public import SerrePositivity.KST.SConstruction.KStageHomotopyFunctor
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-! # 全段の基点固定成分の等号から同じ整数 π 作用の等号へ
概要：同じ始域・終域の BF 射が全段で同じ成分なら、全整数 π 作用が等しい。
方針：元の整数次数の指定段表示を用い、同じ段の基点固定ホモトピー不変性を使う。
規約：BF 写像空間全体の成分等号は要求しない。使われ方：整数群比較の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra Spectra.PointedMapping

/-- 全段で同じ点つき成分の実 BF 射は、全整数 π に同じ作用を誘導する。 -/
lemma spectrumHomotopyMap_eq_of_levelwise_component {X Y : OmegaSpectrum.{u}}
    (f g : X ⟶ Y) (h : ∀ n, componentOf (f.app n) = componentOf (g.app n)) (j : ℤ) :
    OmegaSpectrum.homotopyMap f j = OmegaSpectrum.homotopyMap g j := by
  apply MonoidHom.ext
  intro a
  rw [OmegaSpectrum.homotopyMap_apply, OmegaSpectrum.homotopyMap_apply]
  exact congrFun (pointedHomotopyMap_eq_of_component (h (OmegaSpectrum.canonicalLevel j))
    (OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j))) a

end SerrePositivity.KST.SConstruction
