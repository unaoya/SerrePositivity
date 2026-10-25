module

public import SerrePositivity.BhattScholze.Delta.DeltaWittGhostNaturality
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWittGhostTriangular
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeUniversal

/-! # 任意の元のδjetとWitt jetの三角形比較

自由変数の三角形表示をδ評価し、通常射の下での下位jet消滅を扱う。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 任意の元の第nWitt係数は、δ^nと下位δjetの有限多項式評価の和。 -/
theorem deltaWittGhostVector_coeff_eq_delta_iterate_add_lower (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (a : A) (n : ℕ) :
    (deltaWittGhostVector D a).coeff n = D.delta^[n] a +
      MvPolynomial.eval₂Hom (RingHom.id A) (fun z : Unit × Fin n => D.delta^[z.2.val] a)
        (relativeFreeWittGhostLowerPolynomial D hp () n) := by
  let f := relativeFreeDeltaEval D (RingHom.id A) (fun _ : Unit => a)
  have hf : (relativeFreeDeltaStructure Unit D).IsDeltaHom D f :=
    relativeFreeDeltaEval_isDeltaHom D D (RingHom.id A) (fun _ => rfl) (fun _ => a)
  have he := deltaWittGhostVector_coeff_map (relativeFreeDeltaStructure Unit D) D f hf hg
    (MvPolynomial.X ((), 0)) n
  have hx : f (MvPolynomial.X ((), 0)) = a := by simp [f]
  rw [hx] at he
  change f (relativeFreeWittGhostCoefficient D () n) = _ at he
  rw [relativeFreeWittGhostCoefficient_eq_X_add_lower D hp, map_add] at he
  simpa only [f, relativeFreeDeltaEval_X, relativeFreeDeltaEval,
    relativeFreeFiniteInitialPolynomialMap, MvPolynomial.eval₂Hom_rename,
    MvPolynomial.eval₂Hom_X', Function.comp_def] using he.symm

/-- 自由三角形補正多項式の零δjetでの評価は零。 -/
theorem deltaWittGhostLowerPolynomial_eval_zero (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (n : ℕ) :
    MvPolynomial.eval₂Hom (RingHom.id A) (fun _ : Unit × Fin n => (0 : A))
      (relativeFreeWittGhostLowerPolynomial D hp () n) = 0 := by
  have hi (i : ℕ) : D.delta^[i] (0 : A) = 0 := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, D.delta_zero]
  have hw : deltaWittGhostVector D (0 : A) = 0 := (deltaWittGhostRingHom D hg).map_zero
  have he := deltaWittGhostVector_coeff_eq_delta_iterate_add_lower D hp hg (0 : A) n
  rw [hw, WittVector.zero_coeff, hi, zero_add] at he
  have hv : (fun z : Unit × Fin n => D.delta^[z.2.val] (0 : A)) = fun _ => 0 := by
    funext z
    exact hi z.2.val
  rw [hv] at he
  exact he.symm

/-- 下位δjetを消す任意通常射では、第nWitt係数とδ^nの像が一致する。 -/
theorem deltaWittGhostVector_coeff_map_eq_of_lower_jets_zero {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) (n : ℕ) (hjets : ∀ i < n, q (D.delta^[i] a) = 0) :
    q ((deltaWittGhostVector D a).coeff n) = q (D.delta^[n] a) := by
  rw [deltaWittGhostVector_coeff_eq_delta_iterate_add_lower D hp hg, map_add,
    MvPolynomial.map_eval₂Hom]
  have hv : (fun z : Unit × Fin n => q (D.delta^[z.2.val] a)) = fun _ => 0 := by
    funext z
    exact hjets z.2.val z.2.isLt
  rw [hv]
  have he := congrArg q (deltaWittGhostLowerPolynomial_eval_zero D hp hg n)
  rw [MvPolynomial.map_eval₂Hom, map_zero] at he
  rw [he, add_zero]

/-- 有限深さの全δjet消滅と全Witt係数消滅は任意通常射の下で同値。 -/
theorem deltaWittGhostVector_jets_zero_iff {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) (N : ℕ) :
    (∀ i ≤ N, q (D.delta^[i] a) = 0) ↔
      (∀ i ≤ N, q ((deltaWittGhostVector D a).coeff i) = 0) := by
  constructor
  · intro h i hi
    rw [deltaWittGhostVector_coeff_map_eq_of_lower_jets_zero D hp hg q a i
      (fun j hj => h j (Nat.le_trans (Nat.le_of_lt hj) hi))]
    exact h i hi
  · intro h i hi
    induction i using Nat.strong_induction_on with
    | h i ih =>
        have he := deltaWittGhostVector_coeff_map_eq_of_lower_jets_zero D hp hg q a i
          (fun j hj => ih j hj (Nat.le_trans (Nat.le_of_lt hj) hi))
        rw [h i hi] at he
        exact he.symm

/-- 有限δjet消滅は、係数射を適用したWitt元の対応する切り詰めが零になる条件。 -/
theorem deltaWittGhostVector_jets_zero_iff_truncate_map_zero {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) (N : ℕ) :
    (∀ i ≤ N, q (D.delta^[i] a) = 0) ↔
      WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D a)) = 0 := by
  rw [deltaWittGhostVector_jets_zero_iff D hp hg]
  change _ ↔ WittVector.map q (deltaWittGhostVector D a) ∈ RingHom.ker (WittVector.truncate (N + 1))
  rw [WittVector.mem_ker_truncate]
  simp only [WittVector.map_coeff, Nat.lt_succ_iff]

end SerrePositivity.BhattScholze
