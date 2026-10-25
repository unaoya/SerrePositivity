module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteNormalizedInitialFlat

/-! # 適切な共通係数商上の全有限正規化商の忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- A/(p,d,a_s)から任意有限段への標準係数射。 -/
def deltaDivisionFiniteNormalizedBaseMap (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      DeltaDivisionFiniteNormalizedQuotient D d a u N :=
  (deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.zero_le N)).comp
    (deltaDivisionFiniteNormalizedInitialBaseMap D d a u)

/-- 任意有限段への係数射は、元の基底係数の標準商像に一致する。 -/
theorem deltaDivisionFiniteNormalizedBaseMap_mk (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (b : A) :
    deltaDivisionFiniteNormalizedBaseMap D d a u N (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  rw [deltaDivisionFiniteNormalizedBaseMap, RingHom.comp_apply,
    deltaDivisionFiniteNormalizedInitialBaseMap_mk, deltaDivisionFiniteNormalizedTowerMap_mk]
  congr 1
  simp [deltaDivisionFiniteNormalizedTowerInclusion]

/-- 標準有限商射は適切な共通係数商からの係数射に両立する。 -/
theorem deltaDivisionFiniteNormalizedBaseMap_comp (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    (deltaDivisionFiniteNormalizedTowerMap D d a u h).comp
      (deltaDivisionFiniteNormalizedBaseMap D d a u n) =
        deltaDivisionFiniteNormalizedBaseMap D d a u m := by
  unfold deltaDivisionFiniteNormalizedBaseMap
  rw [← RingHom.comp_assoc, deltaDivisionFiniteNormalizedTowerMap_comp]

/-- 適切な共通係数商上の各有限正規化商の標準代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteNormalizedBaseAlgebra (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u N) :=
  (deltaDivisionFiniteNormalizedBaseMap D d a u N).toAlgebra

/-- 全ての有限正規化商はA/(p,d,a_s)上忠実平坦。零係数商も含む。 -/
theorem deltaDivisionFiniteNormalized_moduleFaithfullyFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u N) := by
  let := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.zero_le N)
  let := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  let : IsScalarTower (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u 0)
      (DeltaDivisionFiniteNormalizedQuotient D d a u N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := deltaDivisionFiniteNormalizedInitial_moduleFaithfullyFlat D d a u
  let := deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat D d a u (Nat.zero_le N)
  exact Module.FaithfullyFlat.trans _ (DeltaDivisionFiniteNormalizedQuotient D d a u 0) _

/-- 全ての有限正規化商はA/(p,d,a_s)上平坦。 -/
theorem deltaDivisionFiniteNormalized_moduleFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    Module.Flat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u N) := by
  let := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  let := deltaDivisionFiniteNormalized_moduleFaithfullyFlat D d a u N
  infer_instance

/-- 適切な共通係数商から各有限段への標準係数射は単射。 -/
theorem deltaDivisionFiniteNormalizedBaseMap_injective (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Function.Injective (deltaDivisionFiniteNormalizedBaseMap D d a u N) := by
  let := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  let := deltaDivisionFiniteNormalized_moduleFaithfullyFlat D d a u N
  exact FaithfulSMul.algebraMap_injective
    (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (DeltaDivisionFiniteNormalizedQuotient D d a u N)

end SerrePositivity.BhattScholze
