module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaFrobeniusNaturality
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaDirectLimit

/-! # δ環のFrobenius余極限

任意のδ環をFrobenius持上げの反復で完全化する代数的構成。
Mathlibの環の有向余極限を再利用し、W₂切断を余極限へ移す。
p進完備化・prismのイデアル・perfectoid対応はここでは扱わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- Frobenius持上げの反復に沿った環の余極限。 -/
abbrev DeltaPerfection (D : DeltaStructure p A) :=
  Ring.DirectLimit (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i])

/-- 第n段からδ完全化への標準環射。 -/
def deltaPerfectionOf (D : DeltaStructure p A) (n : ℕ) : A →+* DeltaPerfection D :=
  Ring.DirectLimit.of (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) n

/-- Frobenius反復の像は余極限の遷移で同一視される。 -/
theorem deltaPerfectionOf_iterate (D : DeltaStructure p A) {i j : ℕ} (hij : i ≤ j)
    (x : A) :
    deltaPerfectionOf D j ((D.frobeniusLift : A → A)^[j - i] x) =
      deltaPerfectionOf D i x := by
  exact Ring.DirectLimit.of_f (G := fun _ : ℕ ↦ A)
    (f := fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) hij x

/-- 隣接段のFrobenius像の同一視。 -/
@[simp] theorem deltaPerfectionOf_succ_frobenius (D : DeltaStructure p A) (n : ℕ) (x : A) :
    deltaPerfectionOf D (n + 1) (D.frobeniusLift x) = deltaPerfectionOf D n x := by
  simpa using deltaPerfectionOf_iterate D (Nat.le_succ n) x

/-- δ完全化のW₂切断。全段での切断の自然性から余極限上へ延長する。 -/
def deltaPerfectionSection (D : DeltaStructure p A) :
    DeltaPerfection D →+* WittTwo p (DeltaPerfection D) :=
  deltaDirectLimitSection (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x)

/-- 切断は第n段で元の切断と一致する。 -/
@[simp] theorem deltaPerfectionSection_of (D : DeltaStructure p A) (n : ℕ) (x : A) :
    deltaPerfectionSection D (deltaPerfectionOf D n x) =
      wittTwoMap (deltaPerfectionOf D n) (D.sectionHom x) :=
  deltaDirectLimitSection_of (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x) n x

/-- Frobenius余極限のδ構造。 -/
def deltaPerfectionStructure (D : DeltaStructure p A) : DeltaStructure p (DeltaPerfection D) :=
  deltaDirectLimitStructure (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x)

/-- 全ての標準段射はδ射。 -/
theorem deltaPerfectionOf_isDeltaHom (D : DeltaStructure p A) (n : ℕ) :
    D.IsDeltaHom (deltaPerfectionStructure D) (deltaPerfectionOf D n) :=
  deltaDirectLimitOf_isDeltaHom (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x) n

/-- 完全化のFrobeniusは各段で元のFrobeniusを適用する。 -/
@[simp] theorem deltaPerfection_frobenius_of (D : DeltaStructure p A) (n : ℕ) (x : A) :
    (deltaPerfectionStructure D).frobeniusLift (deltaPerfectionOf D n x) =
      deltaPerfectionOf D n (D.frobeniusLift x) :=
  ((deltaPerfectionOf_isDeltaHom D n).map_frobeniusLift x).symm

/-- 段を一つ進める環射。Frobeniusの逆に相当する。 -/
def deltaPerfectionShift (D : DeltaStructure p A) : DeltaPerfection D →+* DeltaPerfection D :=
  Ring.DirectLimit.lift _ _ _ (fun n ↦ deltaPerfectionOf D (n + 1)) (by
    intro i j hij x
    have h := deltaPerfectionOf_iterate D (Nat.add_le_add_right hij 1) x
    simpa only [Nat.add_sub_add_right] using h)

/-- 段送り射の具体的な式。 -/
@[simp] theorem deltaPerfectionShift_of (D : DeltaStructure p A) (n : ℕ) (x : A) :
    deltaPerfectionShift D (deltaPerfectionOf D n x) = deltaPerfectionOf D (n + 1) x :=
  by
    exact Ring.DirectLimit.lift_of (G := fun _ : ℕ ↦ A)
      (f := fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) _ _ _ n x

/-- 段送り射はFrobeniusの左逆。 -/
theorem deltaPerfectionShift_leftInverse (D : DeltaStructure p A) :
    Function.LeftInverse (deltaPerfectionShift D) (deltaPerfectionStructure D).frobeniusLift := by
  intro x
  obtain ⟨n, a, rfl⟩ := Ring.DirectLimit.exists_of x
  change deltaPerfectionShift D ((deltaPerfectionStructure D).frobeniusLift
    (deltaPerfectionOf D n a)) = deltaPerfectionOf D n a
  rw [deltaPerfection_frobenius_of, deltaPerfectionShift_of, deltaPerfectionOf_succ_frobenius]

/-- 段送り射はFrobeniusの右逆。 -/
theorem deltaPerfectionShift_rightInverse (D : DeltaStructure p A) :
    Function.RightInverse (deltaPerfectionShift D) (deltaPerfectionStructure D).frobeniusLift := by
  intro x
  obtain ⟨n, a, rfl⟩ := Ring.DirectLimit.exists_of x
  change (deltaPerfectionStructure D).frobeniusLift
    (deltaPerfectionShift D (deltaPerfectionOf D n a)) = deltaPerfectionOf D n a
  rw [deltaPerfectionShift_of, deltaPerfection_frobenius_of, deltaPerfectionOf_succ_frobenius]

/-- Frobenius余極限は完全δ環。 -/
theorem deltaPerfection_isPerfect (D : DeltaStructure p A) :
    (deltaPerfectionStructure D).IsPerfect :=
  ⟨(deltaPerfectionShift_leftInverse D).injective,
    (deltaPerfectionShift_rightInverse D).surjective⟩

end SerrePositivity.BhattScholze
