module

public import SerrePositivity.KST.LocalizingInvariants.ProFiberSequence
public import SerrePositivity.KST.LocalizingInvariants.ProGroupExactZero

/-!
概要：実 pro fiber 列の各項の π-pro 零性と、射影の eventual な核の零化。
方針：元の包含・射影の自然性と全空間の位置の完全性を可換群の pro 補題へ渡す。
規約：接続射の未証明の自然性は使わない。使われ方：pro 切除の pro 同値判定の前半。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.LocalizingInvariants.ProFiberSequence
variable (D : ProFiberSequence.{u})

lemma projection_eventuallyKernelTrivial
    (hF : ProSpectrum.IsPiProZero (vertex D 0 0)) (j : ℤ) :
    ProGroup.IsEventuallyKernelTrivial (groupProjection D j) :=
  ProGroup.eventuallyKernelTrivial_of_exact_proZero (groupInclusion D j) (groupProjection D j)
    (exact_total D · j) (hF j)

lemma inclusion_eventuallyImageSurjective
    (hB : ProSpectrum.IsPiProZero (vertex D 1 1)) (j : ℤ) :
    ProGroup.IsEventuallyImageSurjective (groupInclusion D j) :=
  ProGroup.eventuallyImageSurjective_of_exact_proZero (groupInclusion D j) (groupProjection D j)
    (exact_total D · j) (hB j)

lemma total_piProZero (hF : ProSpectrum.IsPiProZero (vertex D 0 0))
    (hB : ProSpectrum.IsPiProZero (vertex D 1 1)) :
    ProSpectrum.IsPiProZero (vertex D 1 0) := fun j =>
  ProGroup.proZero_of_exact (groupInclusion D j) (groupProjection D j)
    (exact_total D · j) (hF j) (hB j)

end SerrePositivity.KST.LocalizingInvariants.ProFiberSequence
