module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivisionReindex

/-! # raw再添字射の恒等・合成公式 -/

@[expose] public noncomputable section
universe u v w z
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable {σ : Type v} {τ : Type w} {υ : Type z}
variable (D : DeltaStructure p A) (d : A)

/-- 恒等添字写像に沿うraw再添字射は恒等射。 -/
theorem deltaAdjoinDivisionReindex_id (a : σ → A) :
    deltaAdjoinDivisionReindex D d a a id (fun _ ↦ rfl) =
      RingHom.id (DeltaAdjoinDivision D d a) := by
  have h := deltaAdjoinDivisionReindex_spec D d a a id (fun _ ↦ rfl)
  apply deltaAdjoinDivisionHom_ext D (deltaAdjoinDivisionStructure D d a) d a _ _
    h.1 (deltaAdjoinDivisionStructure D d a).isDeltaHom_id
  · rw [h.2.1, RingHom.id_comp]
  · intro s
    exact h.2.2 s

/-- raw再添字射の合成は、添字写像の合成に沿う標準射。 -/
theorem deltaAdjoinDivisionReindex_comp (a : σ → A) (b : τ → A) (c : υ → A)
    (ρ : σ → τ) (κ : τ → υ) (hρ : ∀ s, a s = b (ρ s)) (hκ : ∀ t, b t = c (κ t)) :
    (deltaAdjoinDivisionReindex D d b c κ hκ).comp
      (deltaAdjoinDivisionReindex D d a b ρ hρ) =
        deltaAdjoinDivisionReindex D d a c (κ ∘ ρ) (fun s ↦ (hρ s).trans (hκ (ρ s))) := by
  have hf := deltaAdjoinDivisionReindex_spec D d a b ρ hρ
  have hg := deltaAdjoinDivisionReindex_spec D d b c κ hκ
  have hh := deltaAdjoinDivisionReindex_spec D d a c (κ ∘ ρ)
    (fun s ↦ (hρ s).trans (hκ (ρ s)))
  apply deltaAdjoinDivisionHom_ext D (deltaAdjoinDivisionStructure D d c) d a _ _
    (hg.1.comp hf.1) hh.1
  · rw [RingHom.comp_assoc, hf.2.1, hg.2.1, hh.2.1]
  · intro s
    rw [RingHom.comp_apply, hf.2.2, hg.2.2, hh.2.2]
    rfl

end SerrePositivity.BhattScholze
