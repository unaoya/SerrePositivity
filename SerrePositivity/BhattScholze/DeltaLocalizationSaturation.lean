module

public import SerrePositivity.BhattScholze.DeltaLocalization

/-! # 任意の分母集合のFrobenius安定化

著者公開版Remark 2.16のT={S,φ(S),φ²(S),…}の代数的構成。
Tでの局所化はSを単元に送るδ基底射について普遍である。
p局所化・p完備化との比較は主張しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 分母集合のFrobenius反復像を含む乗法的閉包。 -/
def frobeniusDenominators (D : DeltaStructure p R) (M : Submonoid R) : Submonoid R :=
  Submonoid.closure (Set.range (fun t : M × ℕ ↦ (D.frobeniusLift : R → R)^[t.2] t.1))

/-- 元の分母集合はFrobenius安定化に含まれる。 -/
theorem le_frobeniusDenominators (D : DeltaStructure p R) (M : Submonoid R) :
    M ≤ D.frobeniusDenominators M := by
  intro s hs
  exact Submonoid.subset_closure ⟨(⟨s, hs⟩, 0), rfl⟩

/-- 安定化した分母集合はFrobeniusで安定。 -/
theorem frobeniusDenominators_stable (D : DeltaStructure p R) (M : Submonoid R)
    (s : D.frobeniusDenominators M) :
    D.frobeniusLift s ∈ D.frobeniusDenominators M := by
  have h : D.frobeniusDenominators M ≤
      (D.frobeniusDenominators M).comap D.frobeniusLift.toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro x ⟨⟨r, n⟩, rfl⟩
    apply Submonoid.subset_closure
    exact ⟨(r, n + 1), Function.iterate_succ_apply' _ _ _⟩
  exact h s.property

/-- 安定化はMを含む最小のFrobenius安定乗法集合。 -/
theorem frobeniusDenominators_le (D : DeltaStructure p R) (M N : Submonoid R)
    (hMN : M ≤ N) (hN : ∀ s : N, D.frobeniusLift s ∈ N) :
    D.frobeniusDenominators M ≤ N := by
  apply Submonoid.closure_le.mpr
  rintro x ⟨⟨s, n⟩, rfl⟩
  induction n with
  | zero => exact hMN s.property
  | succ n ih =>
    change (D.frobeniusLift : R → R)^[n + 1] s ∈ N
    rw [Function.iterate_succ_apply']
    exact hN ⟨_, ih⟩

/-- δ射が元の分母を単元に送れば、Frobenius安定化の全分母も単元に送る。 -/
theorem IsDeltaHom.isUnit_frobeniusDenominators {A : Type w} [CommRing A]
    {D : DeltaStructure p R} {E : DeltaStructure p A} {f : R →+* A}
    (hf : D.IsDeltaHom E f) (M : Submonoid R) (hM : ∀ s : M, IsUnit (f s))
    (s : D.frobeniusDenominators M) : IsUnit (f s) := by
  have hiter (r : M) (n : ℕ) : IsUnit (f ((D.frobeniusLift : R → R)^[n] r)) := by
    induction n with
    | zero => exact hM r
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf.map_frobeniusLift]
      exact ih.map E.frobeniusLift
  exact Submonoid.closure_induction
    (fun x hx ↦ by obtain ⟨⟨r, n⟩, rfl⟩ := hx; exact hiter r n)
    (by simp)
    (fun x y _ _ hx hy ↦ by rw [map_mul]; exact hx.mul hy) s.property

/-- 任意のMを反復像で安定化して局所化すると、Mを単元に送るδ射の普遍対象となる。
源・標準射・局所化δ構造を具体的に明示する。 -/
theorem existsUnique_saturatedLocalization_lift (D : DeltaStructure p R) (M : Submonoid R)
    (B : Type v) [CommRing B] [Algebra R B] [IsLocalization (D.frobeniusDenominators M) B]
    {A : Type w} [CommRing A] (E : DeltaStructure p A) (f : R →+* A)
    (hf : D.IsDeltaHom E f) (hM : ∀ s : M, IsUnit (f s)) :
    ∃! g : B →+* A,
      g.comp (algebraMap R B) = f ∧
        (D.localization (D.frobeniusDenominators M) B
          (D.frobeniusDenominators_stable M)).IsDeltaHom E g :=
  D.existsUnique_localization_lift (D.frobeniusDenominators M) B
    (D.frobeniusDenominators_stable M) E f hf
    (hf.isUnit_frobeniusDenominators M hM)

end SerrePositivity.BhattScholze.DeltaStructure
