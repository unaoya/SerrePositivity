module

public import SerrePositivity.BhattScholze.DeltaDivisionWittRelationElement

/-! # 下位関係イデアル上の次段δ生成元のWitt根関係元への置換

商射での消滅比較により、任意の下位イデアル上で正確なイデアル等式を示す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p,dと下位δ関係式を含むイデアルでは、次段生成元とWitt根関係元の所属は同値。 -/
theorem deltaDivision_next_jet_mem_iff_witt_relation_mem (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (I : Ideal A) (hpI : (p : A) ∈ I) (d x a : A) (hdI : d ∈ I)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, D.delta^[i] (d * x - a) ∈ I) :
    D.delta^[n + 2] (d * x - a) ∈ I ↔ deltaDivisionWittRelationElement D d x a u n ∈ I := by
  have he := deltaDivision_next_jet_zero_iff_witt_relation_map_zero D hp hg
    (Ideal.Quotient.mk I) (Ideal.Quotient.eq_zero_iff_mem.mpr hpI) d x a
    (Ideal.Quotient.eq_zero_iff_mem.mpr hdI) u hu n
    (fun i hi => Ideal.Quotient.eq_zero_iff_mem.mpr (hlower i hi))
  simpa only [Ideal.Quotient.eq_zero_iff_mem] using he

/-- 下位イデアルに次段δ生成元を加える操作は、Witt根関係元を加える操作に一致する。 -/
theorem deltaDivision_next_jet_sup_span_eq_witt_relation (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (I : Ideal A) (hpI : (p : A) ∈ I) (d x a : A) (hdI : d ∈ I)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, D.delta^[i] (d * x - a) ∈ I) :
    I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))} =
      I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} := by
  apply le_antisymm
  · have hI : I ≤ I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} := le_sup_left
    have hS : Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} ≤
        I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} := le_sup_right
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg
      (I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)})
      (hI hpI) d x a (hI hdI) u hu n
      (fun i hi => hI (hlower i hi))).mpr
    exact hS (Ideal.mem_span_singleton_self _)
  · have hI : I ≤ I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))} := le_sup_left
    have hS : Ideal.span {(D.delta^[n + 2] (d * x - a))} ≤
        I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))} := le_sup_right
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg
      (I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))})
      (hI hpI) d x a (hI hdI) u hu n
      (fun i hi => hI (hlower i hi))).mp
    exact hS (Ideal.mem_span_singleton_self _)

/-- 任意族の次段δ生成元は、下位イデアル上で同時にWitt根関係元へ置き換えられる。 -/
theorem deltaDivision_family_next_jets_sup_span_eq_witt_relations {σ : Type v}
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (I : Ideal A) (hpI : (p : A) ∈ I) (d : A) (x a : σ → A) (hdI : d ∈ I)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ s i, i ≤ n + 1 → D.delta^[i] (d * x s - a s) ∈ I) :
    I ⊔ Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) =
      I ⊔ Ideal.span
        (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) := by
  apply le_antisymm
  · have hI : I ≤ I ⊔ Ideal.span
        (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) := le_sup_left
    have hS : Ideal.span
        (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) ≤
        I ⊔ Ideal.span
          (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) :=
      le_sup_right
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg _ (hI hpI)
      d (x s) (a s) (hI hdI) u hu n (fun i hi => hI (hlower s i hi))).mpr
    exact hS (Ideal.subset_span (Set.mem_range.mpr ⟨s, rfl⟩))
  · have hI : I ≤ I ⊔ Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) :=
      le_sup_left
    have hS : Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) ≤
        I ⊔ Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) := le_sup_right
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg _ (hI hpI)
      d (x s) (a s) (hI hdI) u hu n (fun i hi => hI (hlower s i hi))).mp
    exact hS (Ideal.subset_span (Set.mem_range.mpr ⟨s, rfl⟩))

end SerrePositivity.BhattScholze
