module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteNormalizedStepFlat

/-! # 有限正規化商の標準射の直系 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期有限多項式環の任意の後段への標準包含。 -/
def deltaDivisionFiniteNormalizedTowerInclusion (n m : ℕ) (h : n ≤ m) :
    MvPolynomial (σ × Fin (n + 1)) A →+* MvPolynomial (σ × Fin (m + 1)) A :=
  (MvPolynomial.rename fun z => (z.1, z.2.castLE (Nat.succ_le_succ h))).toRingHom

/-- 標準一段射を反復した、有限正規化商の任意の後段への射。 -/
def deltaDivisionFiniteNormalizedTowerMap (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    DeltaDivisionFiniteNormalizedQuotient D d a u n →+*
      DeltaDivisionFiniteNormalizedQuotient D d a u m :=
  Nat.leRec (motive := fun m _ => DeltaDivisionFiniteNormalizedQuotient D d a u n →+*
    DeltaDivisionFiniteNormalizedQuotient D d a u m)
    (RingHom.id _) (fun {k} _ f => (deltaDivisionFiniteNormalizedStepMap D d a u k).comp f) h

/-- 同じ有限段への標準射は恒等射。 -/
@[simp] theorem deltaDivisionFiniteNormalizedTowerMap_self (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (n : ℕ) :
    deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_refl n) = RingHom.id _ := by
  simp only [deltaDivisionFiniteNormalizedTowerMap, Nat.leRec_self]

/-- 後段を一段進めた射は標準一段射との合成。 -/
theorem deltaDivisionFiniteNormalizedTowerMap_succ (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_succ_of_le h) =
      (deltaDivisionFiniteNormalizedStepMap D d a u m).comp
        (deltaDivisionFiniteNormalizedTowerMap D d a u h) := by
  simp only [deltaDivisionFiniteNormalizedTowerMap, Nat.leRec_succ _ _ h]

/-- 標準有限商射は任意三段の合成に整合する。 -/
theorem deltaDivisionFiniteNormalizedTowerMap_comp (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    (deltaDivisionFiniteNormalizedTowerMap D d a u hmk).comp
      (deltaDivisionFiniteNormalizedTowerMap D d a u hnm) =
        deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_trans hnm hmk) := by
  induction hmk using Nat.leRec with
  | refl => rw [deltaDivisionFiniteNormalizedTowerMap_self, RingHom.id_comp]
  | le_succ_of_le h ih =>
      rw [deltaDivisionFiniteNormalizedTowerMap_succ D d a u h,
        deltaDivisionFiniteNormalizedTowerMap_succ D d a u (Nat.le_trans hnm h),
        RingHom.comp_assoc, ih]

/-- 標準有限商射は全て単射。 -/
theorem deltaDivisionFiniteNormalizedTowerMap_injective (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    Function.Injective (deltaDivisionFiniteNormalizedTowerMap D d a u h) := by
  induction h using Nat.leRec with
  | refl => rw [deltaDivisionFiniteNormalizedTowerMap_self]; exact Function.injective_id
  | le_succ_of_le h ih =>
      rw [deltaDivisionFiniteNormalizedTowerMap_succ D d a u h]
      exact (deltaDivisionFiniteNormalizedStepMap_injective D d a u _).comp ih

/-- 任意後段への商射も、有限多項式環の標準rename包含に両立する。 -/
theorem deltaDivisionFiniteNormalizedTowerMap_mk (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m)
    (f : MvPolynomial (σ × Fin (n + 1)) A) :
    deltaDivisionFiniteNormalizedTowerMap D d a u h (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (deltaDivisionFiniteNormalizedTowerInclusion n m h f) := by
  induction h using Nat.leRec with
  | refl =>
      rw [deltaDivisionFiniteNormalizedTowerMap_self]
      change Ideal.Quotient.mk _ f = Ideal.Quotient.mk _ (MvPolynomial.rename _ f)
      congr 1
      change f = MvPolynomial.rename (fun z : σ × Fin (n + 1) => (z.1, z.2)) f
      exact (MvPolynomial.rename_id_apply f).symm
  | le_succ_of_le h ih =>
      rw [deltaDivisionFiniteNormalizedTowerMap_succ D d a u h, RingHom.comp_apply, ih,
        deltaDivisionFiniteNormalizedStepMap_mk]
      congr 1
      unfold relativeFreeFiniteStepInclusion deltaDivisionFiniteNormalizedTowerInclusion
      change MvPolynomial.rename _ (MvPolynomial.rename _ f) = MvPolynomial.rename _ f
      rw [MvPolynomial.rename_rename]
      rfl

end SerrePositivity.BhattScholze
