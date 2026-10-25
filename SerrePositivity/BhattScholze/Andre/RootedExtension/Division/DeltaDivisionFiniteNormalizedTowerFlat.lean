module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteNormalizedTowerMaps

/-! # 標準有限商直系の任意二段間の忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意二段間の標準商射による代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteNormalizedTowerAlgebra (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    Algebra (DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (DeltaDivisionFiniteNormalizedQuotient D d a u m) :=
  (deltaDivisionFiniteNormalizedTowerMap D d a u h).toAlgebra

/-- 標準商射の合成は、後続一段についての係数塔の可換性を与える。 -/
theorem deltaDivisionFiniteNormalizedTower_scalarTower_succ (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a u m
    letI := deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.le_succ_of_le h)
    IsScalarTower (DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (DeltaDivisionFiniteNormalizedQuotient D d a u m)
      (DeltaDivisionFiniteNormalizedQuotient D d a u (m + 1)) := by
  let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a u m
  let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.le_succ_of_le h)
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_succ_of_le h) b =
    deltaDivisionFiniteNormalizedStepMap D d a u m
      (deltaDivisionFiniteNormalizedTowerMap D d a u h b)
  exact RingHom.congr_fun (deltaDivisionFiniteNormalizedTowerMap_succ D d a u h) b

/-- 任意二段間の標準有限商射は忠実平坦。零商を含む。 -/
theorem deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
    Module.FaithfullyFlat (DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (DeltaDivisionFiniteNormalizedQuotient D d a u m) := by
  induction h using Nat.leRec with
  | refl =>
      simp +instances only [deltaDivisionFiniteNormalizedTowerAlgebra,
        deltaDivisionFiniteNormalizedTowerMap_self]
      infer_instance
  | @le_succ_of_le k h ih =>
      let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
      let := deltaDivisionFiniteNormalizedStepAlgebra D d a u k
      let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.le_succ_of_le h)
      let := deltaDivisionFiniteNormalizedTower_scalarTower_succ D d a u h
      let := ih
      let := deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a u k
      exact Module.FaithfullyFlat.trans _ (DeltaDivisionFiniteNormalizedQuotient D d a u k) _

/-- 任意二段間の標準有限商射は平坦。 -/
theorem deltaDivisionFiniteNormalizedTower_moduleFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
    Module.Flat (DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (DeltaDivisionFiniteNormalizedQuotient D d a u m) := by
  let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
  let := deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat D d a u h
  infer_instance

end SerrePositivity.BhattScholze
