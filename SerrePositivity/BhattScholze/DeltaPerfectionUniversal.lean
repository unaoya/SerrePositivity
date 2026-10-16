module

public import SerrePositivity.BhattScholze.DeltaPerfection

/-! # δ完全化の普遍性

具体的なFrobenius余極限から任意の完全δ環への基底δ射の一意な延長。
完全化は余極限であり、Mathlibのtiltに使う逆極限Perfectionとは区別する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B]

/-- 完全δ終域への第n段の射。逆Frobeniusをn回適用する。 -/
def deltaPerfectionStage (E : DeltaStructure p B) (hE : E.IsPerfect) (f : A →+* B) :
    ℕ → A →+* B
  | 0 => f
  | n + 1 => (E.frobeniusEquiv hE).symm.toRingHom.comp (deltaPerfectionStage E hE f n)

/-- 各段の射はδ射。 -/
theorem deltaPerfectionStage_isDeltaHom {D : DeltaStructure p A} {E : DeltaStructure p B}
    (hE : E.IsPerfect) {f : A →+* B} (hf : D.IsDeltaHom E f) (n : ℕ) :
    D.IsDeltaHom E (deltaPerfectionStage E hE f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (E.frobeniusEquiv_symm_isDeltaHom hE).comp ih

/-- 第n+1段の射はFrobenius遷移に沿って第n段の射と一致する。 -/
theorem deltaPerfectionStage_step {D : DeltaStructure p A} {E : DeltaStructure p B}
    (hE : E.IsPerfect) {f : A →+* B} (hf : D.IsDeltaHom E f) (n : ℕ) (x : A) :
    deltaPerfectionStage E hE f (n + 1) (D.frobeniusLift x) =
      deltaPerfectionStage E hE f n x := by
  change (E.frobeniusEquiv hE).symm
    (deltaPerfectionStage E hE f n (D.frobeniusLift x)) = _
  rw [(deltaPerfectionStage_isDeltaHom hE hf n).map_frobeniusLift]
  exact (E.frobeniusEquiv hE).symm_apply_apply _

/-- 全段の射はFrobenius反復遷移と両立する。 -/
theorem deltaPerfectionStage_compatible {D : DeltaStructure p A} {E : DeltaStructure p B}
    (hE : E.IsPerfect) {f : A →+* B} (hf : D.IsDeltaHom E f)
    (i j : ℕ) (hij : i ≤ j) (x : A) :
    deltaPerfectionStage E hE f j ((D.frobeniusLift : A → A)^[j - i] x) =
      deltaPerfectionStage E hE f i x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, Function.iterate_succ_apply', deltaPerfectionStage_step hE hf]
    exact ih

/-- 任意のδ基底射fから完全δ終域への一意な射が、具体的なδ完全化から存在する。 -/
theorem existsUnique_deltaPerfectionHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) (f : A →+* B) (hf : D.IsDeltaHom E f) :
    ∃! g : DeltaPerfection D →+* B,
      (deltaPerfectionStructure D).IsDeltaHom E g ∧ g.comp (deltaPerfectionOf D 0) = f := by
  let g : DeltaPerfection D →+* B := Ring.DirectLimit.lift _ _ B
    (deltaPerfectionStage E hE f) (deltaPerfectionStage_compatible hE hf)
  have hg (n : ℕ) (x : A) : g (deltaPerfectionOf D n x) = deltaPerfectionStage E hE f n x := by
    unfold g deltaPerfectionOf
    rw [Ring.DirectLimit.lift_of]
  have hgd : (deltaPerfectionStructure D).IsDeltaHom E g :=
    deltaDirectLimitLift_isDeltaHom (fun _ : ℕ ↦ A)
      (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
      (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x) E
      (deltaPerfectionStage E hE f) (deltaPerfectionStage_compatible hE hf)
      (deltaPerfectionStage_isDeltaHom hE hf)
  have hg0 : g.comp (deltaPerfectionOf D 0) = f := by
    ext x
    exact hg 0 x
  refine ⟨g, ⟨hgd, hg0⟩, ?_⟩
  intro l hl
  have hstage (n : ℕ) (x : A) : l (deltaPerfectionOf D n x) = deltaPerfectionStage E hE f n x := by
    induction n with
    | zero => exact DFunLike.congr_fun hl.2 x
    | succ n ih =>
      apply hE.1
      rw [← hl.1.map_frobeniusLift, deltaPerfection_frobenius_of,
        deltaPerfectionOf_succ_frobenius, ih]
      change deltaPerfectionStage E hE f n x =
        (E.frobeniusEquiv hE) ((E.frobeniusEquiv hE).symm (deltaPerfectionStage E hE f n x))
      exact ((E.frobeniusEquiv hE).apply_symm_apply _).symm
  apply RingHom.ext
  intro x
  obtain ⟨n, a, rfl⟩ := Ring.DirectLimit.exists_of x
  exact (hstage n a).trans (hg n a).symm

/-- 完全δ終域へのδ射は、元の環からの第0段の射上の値で決まる。 -/
theorem deltaPerfectionHom_ext (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) (f g : DeltaPerfection D →+* B)
    (hf : (deltaPerfectionStructure D).IsDeltaHom E f)
    (hg : (deltaPerfectionStructure D).IsDeltaHom E g)
    (hfg : f.comp (deltaPerfectionOf D 0) = g.comp (deltaPerfectionOf D 0)) : f = g := by
  obtain ⟨_, _, hu⟩ := existsUnique_deltaPerfectionHom D E hE
    (g.comp (deltaPerfectionOf D 0)) (hg.comp (deltaPerfectionOf_isDeltaHom D 0))
  exact (hu f ⟨hf, hfg⟩).trans (hu g ⟨hg, rfl⟩).symm

end SerrePositivity.BhattScholze
