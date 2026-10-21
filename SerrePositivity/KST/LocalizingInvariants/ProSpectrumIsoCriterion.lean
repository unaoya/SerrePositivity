module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion
public import SerrePositivity.KST.ProExcision.SpectralPro

/-!
概要：整数 π の pro 同値を eventual な核・余核で判定し、π-pro 零性を比較で移す。
方針：可換群の pro 同型判定と既存の一般 pro 零性移送を次数ごとに適用する。
規約：切断を使う weak equivalence との同定は含めない。使われ方：pro 切除の値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.LocalizingInvariants.ProSpectrum

lemma piProEquivalence_iff_kernel_image {X Y : Tower.{u}} (f : LevelHom X Y) :
    IsPiProEquivalence f ↔ ∀ j : ℤ,
      ProGroup.IsEventuallyKernelTrivial (f.map (SpectrumHo.piFunctor j)) ∧
        ProGroup.IsEventuallyImageSurjective (f.map (SpectrumHo.piFunctor j)) := by
  constructor
  · intro h j
    exact (ProGroup.proIso_iff_kernel_image _).1 (h j)
  · intro h j
    exact (ProGroup.proIso_iff_kernel_image _).2 (h j)

lemma piProZero_of_piProEquivalence {X Y : Tower.{u}} {f : LevelHom X Y}
    (hX : IsPiProZero X) (hf : IsPiProEquivalence f) : IsPiProZero Y := fun j =>
  ProExcision.IsProZero.of_proIso (hX j) (hf j)

end SerrePositivity.KST.LocalizingInvariants.ProSpectrum
