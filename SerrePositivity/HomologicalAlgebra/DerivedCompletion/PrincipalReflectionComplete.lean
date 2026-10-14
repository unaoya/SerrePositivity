module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalReflectionPresentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionRing

/-! # 列の商による主元完備化の完備性

対角線上の有限和を使い、商の列に対する漸化式の逆を構成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 二重列の対角線に沿った有限和。 -/
def diagonalSequence (x : ℕ → ℕ → R) : ℕ → R
  | 0 => x 0 0
  | n + 1 => x 0 (n + 1) + diagonalSequence (fun i ↦ x (i + 1)) n

/-- 対角和の線形写像。 -/
def sequenceDiagonal : (ℕ → ℕ → R) →ₗ[R] (ℕ → R) where
  toFun := diagonalSequence R
  map_add' x y := by
    funext n
    induction n generalizing x y with
    | zero => rfl
    | succ n ih =>
      change (x 0 (n + 1) + y 0 (n + 1)) +
        diagonalSequence R ((fun i ↦ x (i + 1)) + (fun i ↦ y (i + 1))) n = _
      rw [ih]
      change _ = (x 0 (n + 1) + diagonalSequence R (fun i ↦ x (i + 1)) n) +
        (y 0 (n + 1) + diagonalSequence R (fun i ↦ y (i + 1)) n)
      simp only [Pi.add_apply]
      abel
  map_smul' r x := by
    funext n
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      change r • x 0 (n + 1) + diagonalSequence R (r • (fun i ↦ x (i + 1))) n = _
      rw [ih]
      exact (smul_add r _ _).symm

/-- 各行の右シフトは、対角和全体の右シフトになる。 -/
theorem sequenceDiagonal_shift (x : ℕ → ℕ → R) :
    sequenceDiagonal R (fun i ↦ sequenceShiftRight R (x i)) =
      sequenceShiftRight R (sequenceDiagonal R x) := by
  funext n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change x 0 n + sequenceDiagonal R (fun i ↦ sequenceShiftRight R (x (i + 1))) n =
      sequenceDiagonal R x n
    rw [ih (fun i ↦ x (i + 1))]
    cases n <;> simp [sequenceDiagonal, diagonalSequence]

/-- 各行の関係式の対角和も、同じ関係式の像に入る。 -/
theorem sequenceDiagonal_relation (f : R) (x : ℕ → ℕ → R) :
    sequenceDiagonal R (fun i ↦ principalReflectionRelation R f (x i)) =
      principalReflectionRelation R f (sequenceDiagonal R x) := by
  change sequenceDiagonal R ((fun i ↦ sequenceShiftRight R (x i)) - f • x) = _
  rw [map_sub, map_smul, sequenceDiagonal_shift]
  rfl

/-- 各行の商での値が同じなら、対角和の商での値も同じ。 -/
theorem principalReflection_diagonal_congr (f : R) (x y : ℕ → ℕ → R)
    (h : ∀ n, principalReflectionMk R f (x n) = principalReflectionMk R f (y n)) :
    principalReflectionMk R f (sequenceDiagonal R x) =
      principalReflectionMk R f (sequenceDiagonal R y) := by
  have hz : ∀ n, ∃ z, principalReflectionRelation R f z = x n - y n := by
    intro n
    change x n - y n ∈ (principalReflectionRelation R f).range
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change principalReflectionMk R f (x n - y n) = 0
    rw [map_sub, h n, sub_self]
  choose z hz using hz
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  have he : x - y = fun n ↦ principalReflectionRelation R f (z n) := by
    funext n
    exact (hz n).symm
  rw [he, sequenceDiagonal_relation]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨sequenceDiagonal R z, rfl⟩

/-- 商の元の列を、代表元の対角和で足す。 -/
def principalReflectionSum (f : R) (x : ℕ → PrincipalReflectionModule R f) :
    PrincipalReflectionModule R f :=
  principalReflectionMk R f (sequenceDiagonal R
    (fun n ↦ ((principalReflectionRelation R f).range.mkQ_surjective (x n)).choose))

/-- 任意の代表列で対角和を計算できる。 -/
theorem principalReflectionSum_mk (f : R) (x : ℕ → ℕ → R) :
    principalReflectionSum R f (fun n ↦ principalReflectionMk R f (x n)) =
      principalReflectionMk R f (sequenceDiagonal R x) := by
  apply principalReflection_diagonal_congr
  intro n
  exact ((principalReflectionRelation R f).range.mkQ_surjective
    (principalReflectionMk R f (x n))).choose_spec

/-- 対角和は、最初の行と残りの行の右シフトに分かれる。 -/
theorem sequenceDiagonal_decomposition (x : ℕ → ℕ → R) :
    sequenceDiagonal R x = x 0 + sequenceShiftRight R
      (sequenceDiagonal R (fun n ↦ x (n + 1))) := by
  funext n
  cases n <;> simp [sequenceDiagonal, diagonalSequence]

/-- 漸化式の逆候補。 -/
def principalReflectionRecurrenceInverse (f : R) (x : ℕ → PrincipalReflectionModule R f) :
    ℕ → PrincipalReflectionModule R f :=
  fun n ↦ principalReflectionSum R f (fun i ↦ x (n + i))

/-- 逆候補は漸化式の右逆。 -/
theorem principalReflectionRecurrence_rightInverse (f : R) :
    Function.RightInverse (principalReflectionRecurrenceInverse R f) (adicRecurrenceMap f) := by
  intro x
  choose z hz using fun n ↦ (principalReflectionRelation R f).range.mkQ_surjective (x n)
  funext n
  have he : x = fun n ↦ principalReflectionMk R f (z n) := by
    funext n
    exact (hz n).symm
  rw [he]
  change principalReflectionSum R f (fun i ↦ principalReflectionMk R f (z (n + i))) -
    f • principalReflectionSum R f (fun i ↦ principalReflectionMk R f (z ((n + 1) + i))) =
    principalReflectionMk R f (z n)
  rw [principalReflectionSum_mk, principalReflectionSum_mk]
  have hd := congrArg (principalReflectionMk R f)
    (sequenceDiagonal_decomposition R (fun i ↦ z (n + i)))
  simp only [map_add, principalReflectionMk_shift] at hd
  have ht : (fun i ↦ z (n + (i + 1))) = (fun i ↦ z ((n + 1) + i)) := by
    funext i
    congr 1
    omega
  rw [ht] at hd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hd)

/-- 逆候補は漸化式の左逆。 -/
theorem principalReflectionRecurrence_leftInverse (f : R) :
    Function.LeftInverse (principalReflectionRecurrenceInverse R f) (adicRecurrenceMap f) := by
  intro x
  choose z hz using fun n ↦ (principalReflectionRelation R f).range.mkQ_surjective (x n)
  funext n
  have he : x = fun n ↦ principalReflectionMk R f (z n) := by
    funext n
    exact (hz n).symm
  rw [he]
  change principalReflectionSum R f (fun i ↦ principalReflectionMk R f (z (n + i)) -
    f • principalReflectionMk R f (z (n + i + 1))) = principalReflectionMk R f (z n)
  have hs : (fun i ↦ principalReflectionMk R f (z (n + i)) -
      f • principalReflectionMk R f (z (n + i + 1))) =
      fun i ↦ principalReflectionMk R f (z (n + i) - f • z (n + i + 1)) := by
    funext i
    rw [map_sub, map_smul]
  rw [hs, principalReflectionSum_mk]
  change principalReflectionMk R f (sequenceDiagonal R
    ((fun i ↦ z (n + i)) - f • (fun i ↦ z (n + i + 1)))) = _
  rw [map_sub, map_smul, map_sub, map_smul]
  have hd := congrArg (principalReflectionMk R f)
    (sequenceDiagonal_decomposition R (fun i ↦ z (n + i)))
  simp only [map_add, principalReflectionMk_shift] at hd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm, Nat.add_assoc] using hd)

/-- 列による商表示そのものが導来完備。Noether性やtorsion条件は要らない。 -/
theorem principalReflection_isModuleComplete (f : R) :
    IsModuleComplete R f (ModuleCat.of R (PrincipalReflectionModule R f)) := by
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  exact ⟨(principalReflectionRecurrence_leftInverse R f).injective,
    (principalReflectionRecurrence_rightInverse R f).surjective⟩

/-- この商表示は、主元に関する完備加群への反映の条件を実際に満たす。 -/
theorem principalReflection_isCompleteModuleReflection (f : R) :
    IsCompleteModuleReflection R (fun _ : Fin 1 ↦ f)
      (ModuleCat.of R (PrincipalReflectionModule R f)) (principalReflectionUnit R f) where
  isComplete _ := principalReflection_isModuleComplete R f
  universal N hN := principalReflection_evaluation_bijective R f N (hN 0)

end SerrePositivity.DerivedCompletion
