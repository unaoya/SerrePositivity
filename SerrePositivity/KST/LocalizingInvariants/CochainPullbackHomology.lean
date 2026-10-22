module

public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackQuasiIso

/-!
概要：通常 pullback の右射影を、左端と中心のホモロジーが消える次数で同型にする。
方針：左射影の kernel と右脚の kernel の実同型、および両 kernel 包含を比較する。
規約：右脚の次数全射性を使用。使われ方：零集中の底に沿う正の π 次数の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L T : Complex R} (f : K ⟶ T) (g : L ⟶ T)

lemma cochainPullback_snd_quasiIsoAt [Epi g] (i : ℤ)
    (hK : IsZero (K.homology i)) (hKp : IsZero (K.homology (i - 1)))
    (hT : IsZero (T.homology i)) (hTp : IsZero (T.homology (i - 1))) :
    QuasiIsoAt (pullback.snd f g) i := by
  let q := pullback.fst f g
  let sq := IsPullback.of_hasPullback f g
  let k := kernel.map q g (pullback.snd f g) f sq.w
  have : IsIso k := isIso_kernel_map_of_isPullback sq
  have : Epi q := cochainPullback_fst_epi f g
  have := cochainKernelInclusion_quasiIsoAt q i hK hKp
  have := cochainKernelInclusion_quasiIsoAt g i hT hTp
  have : QuasiIsoAt (k ≫ kernel.ι g) i := quasiIsoAt_comp _ _ i
  have he : k ≫ kernel.ι g = kernel.ι q ≫ pullback.snd f g := kernel.lift_ι _ _ _
  have : QuasiIsoAt (kernel.ι q ≫ pullback.snd f g) i := he ▸ ‹QuasiIsoAt (k ≫ kernel.ι g) i›
  exact quasiIsoAt_of_comp_left (kernel.ι q) (pullback.snd f g) i

lemma cochainPullback_fst_quasiIsoAt [Epi g] (i : ℤ)
    (hp : Epi (homologyMap g (i - 1))) (hi : IsIso (homologyMap g i))
    (hn : Mono (homologyMap g (i + 1))) : QuasiIsoAt (pullback.fst f g) i := by
  let q := pullback.fst f g
  let sq := IsPullback.of_hasPullback f g
  let k := kernel.map q g (pullback.snd f g) f sq.w
  have : IsIso k := isIso_kernel_map_of_isPullback sq
  let hS := cochainKernelSequence_shortExact g
  have : IsIso (homologyMap (cochainKernelSequence g).g i) := hi
  have h₀ : (kernel g).ExactAt i := hS.exactAt_X₁ i inferInstance (by
    intro j hj
    have he : j = i - 1 := by change j + 1 = i at hj; omega
    subst j
    exact hp)
  have h₁ : (kernel g).ExactAt (i + 1) := hS.exactAt_X₁ (i + 1) hn (by
    intro j hj
    have he : j = i := by change j + 1 = i + 1 at hj; omega
    subst j
    infer_instance)
  have hq₀ : IsZero ((kernel q).homology i) :=
    ((exactAt_iff_of_quasiIsoAt k i).2 h₀).isZero_homology
  have hq₁ : IsZero ((kernel q).homology (i + 1)) :=
    ((exactAt_iff_of_quasiIsoAt k (i + 1)).2 h₁).isZero_homology
  have : Epi q := cochainPullback_fst_epi f g
  let hQ := cochainKernelSequence_shortExact q
  have : Mono (homologyMap q i) := (hQ.homology_exact₂ i).mono_g (hq₀.eq_of_src _ _)
  have : Epi (homologyMap q i) :=
    (hQ.homology_exact₃ i (i + 1) rfl).epi_f (hq₁.eq_of_tgt _ _)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_of_mono_of_epi _

end SerrePositivity.KST.LocalizingInvariants
