module

public import SerrePositivity.BhattScholze.Delta.DeltaWittGhostRingHom

/-! # δ射に関する構成済みWitt liftの自然性

終域のghost射の単射性だけで点ごとの比較を行う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

private theorem ghost_map_eval (f : A →+* B) (w : WittVector p A) (n : ℕ) :
    WittVector.ghostComponent n (WittVector.map f w) = f (WittVector.ghostComponent n w) := by
  simp only [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow,
    map_sum, map_mul, map_pow, MvPolynomial.aeval_X, map_natCast, WittVector.map_coeff]

/-- δ射によるWitt liftの点ごとの自然性。源のghost単射は不要。 -/
theorem deltaWittGhostVector_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p B → ℕ → B)) (a : A) :
    WittVector.map f (deltaWittGhostVector D a) = deltaWittGhostVector E (f a) := by
  have hi (n : ℕ) : f (D.frobeniusLift^[n] a) = E.frobeniusLift^[n] (f a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf.map_frobeniusLift, ih]
  apply hg
  funext n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply, ghost_map_eval,
    deltaWittGhostVector_ghostComponent, deltaWittGhostVector_ghostComponent]
  exact hi n

/-- 全係数の自然性。自由初期変数の三角形表示をδ反復へ評価する際に使う。 -/
theorem deltaWittGhostVector_coeff_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p B → ℕ → B)) (a : A) (n : ℕ) :
    f ((deltaWittGhostVector D a).coeff n) = (deltaWittGhostVector E (f a)).coeff n := by
  have he := congrArg (fun w : WittVector p B => w.coeff n) (deltaWittGhostVector_map D E f hf hg a)
  simpa only [WittVector.map_coeff] using he

/-- 構成した全Witt環射の自然性の具体的な図式。 -/
theorem deltaWittGhostRingHom_map_comp (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgB : Function.Injective (WittVector.ghostMap : WittVector p B → ℕ → B)) :
    (WittVector.map f).comp (deltaWittGhostRingHom D hgA) =
      (deltaWittGhostRingHom E hgB).comp f := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_map D E f hf hgB a

end SerrePositivity.BhattScholze
