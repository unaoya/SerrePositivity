module

public import SerrePositivity.BhattScholze.PerfectDeltaPDPrism
public import SerrePositivity.BhattScholze.PDCompletionInterface

/-! # 完全δ環の実PD完備化と完備なdistinguished商の比較

標準商がp進完備なら、実完備化後の商と標準商は同型。
古典的完備化への置換ではなく、実H⁰の環普遍性で比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A T : Type u} [CommRing A] [CommRing T]

/-- 完全δ環のdistinguished商の具体的p完備表示は、実PD完備化後の商と同型。 -/
theorem exists_perfectDeltaPDQuotientEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d)
    (f : A →+* T) (hf : Function.Surjective f) (hk : RingHom.ker f = Ideal.span {d})
    [IsAdicComplete (Ideal.span {(p : T)}) T] :
    letI := pdCompletionCommRing A p d
    ∃ e : PDCompletionH0 A p d ⧸ Ideal.span {pdCompletionUnit A p d d} ≃+* T,
      e.toRingHom.comp ((Ideal.Quotient.mk _).comp (pdCompletionUnit A p d)) = f := by
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  let Q := H ⧸ Ideal.span {j d}
  let q := Ideal.Quotient.mk (Ideal.span {j d})
  have hfd : f d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  have hpT := isModuleComplete_of_isAdicComplete T (p : T) (ModuleCat.of T T)
  have hz (B : Type u) [CommRing B] : IsModuleComplete B (0 : B) (ModuleCat.of B B) :=
    isModuleComplete_of_pow_smul_zero B 0 _ 1 (by simp)
  have hdT : IsModuleComplete T (f d) (ModuleCat.of T T) := hfd ▸ hz T
  obtain ⟨g, hg, _⟩ := existsUnique_pdCompletionRingHom A p d T f hpT hdT
  have hgd : g (j d) = 0 := by
    have he : g (j d) = f d := RingHom.congr_fun hg d
    exact he.trans hfd
  let b : Q →+* T := Ideal.Quotient.lift _ g (by
    change Ideal.span {j d} ≤ RingHom.ker g
    rw [Ideal.span_singleton_le_iff_mem]
    exact hgd)
  have hb : b.comp q = g := Ideal.Quotient.lift_comp_mk _ _ _
  have hqjd : q (j d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hi : RingHom.ker f ≤ RingHom.ker (q.comp j) := by
    rw [hk, Ideal.span_singleton_le_iff_mem]
    exact hqjd
  let i : T →+* Q := f.liftOfSurjective hf ⟨q.comp j, hi⟩
  have hij : i.comp f = q.comp j := f.liftOfSurjective_comp hf _
  have hbi : b.comp i = RingHom.id T := by
    apply (RingHom.cancel_right hf).mp
    rw [RingHom.comp_assoc, hij, ← RingHom.comp_assoc, hb, hg, RingHom.id_comp]
  let : IsAdicComplete (Ideal.span {(p : Q)}) Q :=
    perfectDeltaPDPrism_quotient_isAdicComplete D hD d hd
  have hpQ := isModuleComplete_of_isAdicComplete Q (p : Q) (ModuleCat.of Q Q)
  have hdQ : IsModuleComplete Q ((q.comp j) d) (ModuleCat.of Q Q) := hqjd ▸ hz Q
  have hib : i.comp b = RingHom.id Q := by
    apply Ideal.Quotient.ringHom_ext
    have he : (i.comp g) = q := by
      apply pdCompletionRingHom_ext A p d Q (q.comp j) hpQ hdQ
      · rw [RingHom.comp_assoc, hg, hij]
      · rfl
    change (i.comp b).comp q = (RingHom.id Q).comp q
    rw [RingHom.comp_assoc, hb, he, RingHom.id_comp]
  let e : Q ≃+* T :=
    { b with
      invFun := i
      left_inv := RingHom.congr_fun hib
      right_inv := RingHom.congr_fun hbi }
  refine ⟨e, ?_⟩
  change b.comp (q.comp j) = f
  rw [← RingHom.comp_assoc, hb, hg]

end SerrePositivity.BhattScholze
