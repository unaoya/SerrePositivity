module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionSum

/-! # raw δ除算包の再添字付け -/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v} {τ : Type w}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (b : τ → A)
local notation "B" => DeltaAdjoinDivision D d a
local notation "C" => DeltaAdjoinDivision D d b
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "DC" => deltaAdjoinDivisionStructure D d b
local notation "jB" => deltaAdjoinDivisionMap D d a
local notation "jC" => deltaAdjoinDivisionMap D d b
local notation "vB" => deltaAdjoinDivisionVariable D d a
local notation "vC" => deltaAdjoinDivisionVariable D d b

/-- 添字写像と入力の一致で指定される標準δ射の普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionReindex (ρ : σ → τ) (h : ∀ s, a s = b (ρ s)) :
    ∃! f : B →+* C, (DB).IsDeltaHom DC f ∧ f.comp jB = jC ∧
      ∀ s, f (vB s) = vC (ρ s) := by
  apply existsUnique_deltaAdjoinDivisionHom D DC d a jC
    (deltaAdjoinDivisionMap_isDeltaHom D d b)
  intro s
  rw [h s]
  exact deltaAdjoinDivision_relation D d b (ρ s)

/-- 再添字付けによる具体的raw除算δ射。 -/
def deltaAdjoinDivisionReindex (ρ : σ → τ) (h : ∀ s, a s = b (ρ s)) : B →+* C :=
  (existsUnique_deltaAdjoinDivisionReindex D d a b ρ h).choose

/-- 再添字付け射のδ・係数・初期変数の公式。 -/
theorem deltaAdjoinDivisionReindex_spec (ρ : σ → τ) (h : ∀ s, a s = b (ρ s)) :
    (DB).IsDeltaHom DC (deltaAdjoinDivisionReindex D d a b ρ h) ∧
      (deltaAdjoinDivisionReindex D d a b ρ h).comp jB = jC ∧
      ∀ s, deltaAdjoinDivisionReindex D d a b ρ h (vB s) = vC (ρ s) :=
  (existsUnique_deltaAdjoinDivisionReindex D d a b ρ h).choose_spec.1

/-- 添字同値の逆方向を続けると恒等射となる。 -/
theorem deltaAdjoinDivisionReindex_symm_comp (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (deltaAdjoinDivisionReindex D d b a e.symm
      (fun t ↦ by rw [h, e.apply_symm_apply])).comp
      (deltaAdjoinDivisionReindex D d a b e h) = RingHom.id B := by
  have hf := deltaAdjoinDivisionReindex_spec D d a b e h
  have hg := deltaAdjoinDivisionReindex_spec D d b a e.symm
    (fun t ↦ by rw [h, e.apply_symm_apply])
  apply deltaAdjoinDivisionHom_ext D DB d a _ _ (hg.1.comp hf.1) (DB).isDeltaHom_id
  · rw [RingHom.comp_assoc, hf.2.1, hg.2.1, RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, hf.2.2, hg.2.2, e.symm_apply_apply]
    rfl

/-- 逆順の再添字付けも恒等射となる。 -/
theorem deltaAdjoinDivisionReindex_comp_symm (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (deltaAdjoinDivisionReindex D d a b e h).comp
      (deltaAdjoinDivisionReindex D d b a e.symm
        (fun t ↦ by rw [h, e.apply_symm_apply])) = RingHom.id C := by
  have hf := deltaAdjoinDivisionReindex_spec D d a b e h
  have hg := deltaAdjoinDivisionReindex_spec D d b a e.symm
    (fun t ↦ by rw [h, e.apply_symm_apply])
  apply deltaAdjoinDivisionHom_ext D DC d b _ _ (hf.1.comp hg.1) (DC).isDeltaHom_id
  · rw [RingHom.comp_assoc, hg.2.1, hf.2.1, RingHom.id_comp]
  · intro t
    rw [RingHom.comp_apply, hg.2.2, hf.2.2, e.apply_symm_apply]
    rfl

/-- 添字同値は係数と除算変数を保つ標準raw環同型を誘導する。 -/
def deltaAdjoinDivisionReindexEquiv (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) : B ≃+* C :=
  RingEquiv.ofRingHom (deltaAdjoinDivisionReindex D d a b e h)
    (deltaAdjoinDivisionReindex D d b a e.symm (fun t ↦ by rw [h, e.apply_symm_apply]))
    (deltaAdjoinDivisionReindex_comp_symm D d a b e h)
    (deltaAdjoinDivisionReindex_symm_comp D d a b e h)

/-- 再添字同型の両方向はδ構造を保つ。 -/
theorem deltaAdjoinDivisionReindexEquiv_isDeltaHom (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (DB).IsDeltaHom DC (deltaAdjoinDivisionReindexEquiv D d a b e h).toRingHom ∧
      (DC).IsDeltaHom DB (deltaAdjoinDivisionReindexEquiv D d a b e h).symm.toRingHom :=
  ⟨(deltaAdjoinDivisionReindex_spec D d a b e h).1,
    (deltaAdjoinDivisionReindex_spec D d b a e.symm
      (fun t ↦ by rw [h, e.apply_symm_apply])).1⟩

/-- 再添字同型は係数の標準射を保つ。 -/
theorem deltaAdjoinDivisionReindexEquiv_comp (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (deltaAdjoinDivisionReindexEquiv D d a b e h).toRingHom.comp jB = jC :=
  (deltaAdjoinDivisionReindex_spec D d a b e h).2.1

/-- 再添字同型の初期変数上の公式。 -/
theorem deltaAdjoinDivisionReindexEquiv_variable (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) (s : σ) :
    deltaAdjoinDivisionReindexEquiv D d a b e h (vB s) = vC (e s) :=
  (deltaAdjoinDivisionReindex_spec D d a b e h).2.2 s

end SerrePositivity.BhattScholze
