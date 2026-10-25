module

public import SerrePositivity.CommutativeAlgebra.AdicRingHomRange
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
public import SerrePositivity.BhattScholze.Results.SemiperfectoidSurjectivity

/-! # Perfectoidization preserves surjective maps

The actual functorial map has complete image. Its inclusion into the target is
again a universal perfectoidization, so B4 makes this inclusion surjective.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

/-- Every actual map between universal perfectoidizations induced by a
surjection is surjective. No completeness is assumed on the original rings. -/
theorem perfectoidization_map_surjective_of_surjective
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C} {g : B →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q) :
    Function.Surjective (IsPerfectoidization.map hf hg q) := by
  let m := IsPerfectoidization.map hf hg q
  let S := m.range
  let π : C →+* S := m.rangeRestrict
  let ι : S →+* D := m.range.subtype
  have hπ : Function.Surjective π := m.rangeRestrict_surjective
  have hcomm : m.comp f = g.comp q := hf.map_comp hg q
  have hb : ∀ b, g b ∈ m.range := by
    intro b
    obtain ⟨a, rfl⟩ := hq b
    exact ⟨f a, RingHom.congr_fun hcomm a⟩
  let b : B →+* S := g.codRestrict m.range hb
  have hi : IsPerfectoidization p ι := by
    refine ⟨hg.1, ?_⟩
    intro T _ hT k
    obtain ⟨l, hl, huniq⟩ := hg.2 T hT (k.comp b)
    have hlm : l.comp m = k.comp π := by
      apply (hf.2 T hT ((k.comp π).comp f)).unique
      · ext a
        have he := RingHom.congr_fun hl (q a)
        change l (g (q a)) = k (b (q a)) at he
        have hba : b (q a) = π (f a) := by
          apply Subtype.ext
          exact (RingHom.congr_fun hcomm a).symm
        change l (m (f a)) = k (π (f a))
        have hma : m (f a) = g (q a) := RingHom.congr_fun hcomm a
        rw [hma, ← hba]
        exact he
      · rfl
    refine ⟨l, ?_, ?_⟩
    · ext s
      obtain ⟨c, rfl⟩ := hπ s
      exact RingHom.congr_fun hlm c
    · intro l' hl'
      apply huniq
      ext x
      exact RingHom.congr_fun hl' (b x)
  let := hf.1.isAdicComplete C p
  let := hg.1.isAdicComplete D p
  let : IsAdicComplete (Ideal.span {(p : S)}) S := isAdicComplete_ringHom_range p m
  have hι := surjective_of_isPerfectoidization_of_adic_complete_quotient hf.1 π hπ ι hi
  intro d
  obtain ⟨s, hs⟩ := hι d
  obtain ⟨c, hc⟩ := hπ s
  exact ⟨c, by change ι (π c) = d; rw [hc, hs]⟩

end SerrePositivity.BhattScholze
