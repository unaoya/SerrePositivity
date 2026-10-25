module

public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletionUniversal
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaFrobenius

/-! # 完全δ環の実導来(p,d)完備化の完全性

著者公開版Lemma 3.9の完全化後の計算。
逆Frobeniusを実H⁰へ延長し、両合成を環普遍性から恒等射と判定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環の実(p,d)完備化H⁰のδ構造は完全。源の古典的完備性は不要。 -/
theorem deltaPDCompletionStructure_isPerfect (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) :
    letI := pdCompletionCommRing A p d
    (deltaPDCompletionStructure D d).IsPerfect := by
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let DH := deltaPDCompletionStructure D d
  let j := pdCompletionUnit A p d
  let e := D.frobeniusEquiv hD
  have hpH := pdCompletionH0_self_complete_p A p d
  have hdH := pdCompletionH0_self_complete_d A p d
  have hj := pdCompletionUnit_isDeltaHom D d
  let f : A →+* H := j.comp e.symm.toRingHom
  have hf : D.IsDeltaHom DH f := hj.comp (D.frobeniusEquiv_symm_isDeltaHom hD)
  have hd' : IsModuleComplete H (f d) (ModuleCat.of H H) := by
    apply deltaImage_isModuleComplete_of_frobenius D j (e.symm d) hpH
    change IsModuleComplete H (j (e (e.symm d))) (ModuleCat.of H H)
    rw [e.apply_symm_apply]
    exact hdH
  let g := deltaPDCompletionLift D d DH f hf hpH hd'
  have hg : g.comp j = f := deltaPDCompletionLift_comp_unit D d DH f hf hpH hd'
  have hgj (x : A) : g (j x) = j (e.symm x) := RingHom.congr_fun hg x
  have hφj (x : A) : DH.frobeniusLift (j x) = j (e x) := (hj.map_frobeniusLift x).symm
  have hleft : g.comp DH.frobeniusLift = RingHom.id H := by
    apply pdCompletionRingHom_ext A p d H j hpH hdH
    · apply RingHom.ext
      intro x
      change g (DH.frobeniusLift (j x)) = j x
      rw [hφj, hgj, e.symm_apply_apply]
    · exact RingHom.id_comp j
  have hright : DH.frobeniusLift.comp g = RingHom.id H := by
    apply pdCompletionRingHom_ext A p d H j hpH hdH
    · apply RingHom.ext
      intro x
      change DH.frobeniusLift (g (j x)) = j x
      rw [hgj, hφj, e.apply_symm_apply]
    · exact RingHom.id_comp j
  have hl : Function.LeftInverse g DH.frobeniusLift := fun x ↦ RingHom.congr_fun hleft x
  have hr : Function.RightInverse g DH.frobeniusLift := fun x ↦ RingHom.congr_fun hright x
  exact ⟨hl.injective, hr.surjective⟩

end SerrePositivity.BhattScholze
