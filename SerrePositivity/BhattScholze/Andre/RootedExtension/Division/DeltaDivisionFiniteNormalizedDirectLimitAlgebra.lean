module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteNormalizedDirectLimit

/-! # 全段環と有限商直系の共通係数商上の代数射・線形射 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 全段係数射によるA/(p,d,a_s)上の全段環の代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedDirectLimit D d a u) :=
  (deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u).toAlgebra

/-- 標準有限商射は共通係数商上の具体的代数射。 -/
def deltaDivisionFiniteNormalizedTowerAlgHom (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
    DeltaDivisionFiniteNormalizedQuotient D d a u n →ₐ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedQuotient D d a u m := by
  letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
  letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
  exact { deltaDivisionFiniteNormalizedTowerMap D d a u h with
    commutes' := fun b =>
      RingHom.congr_fun (deltaDivisionFiniteNormalizedBaseMap_comp D d a u h) b }

/-- 標準有限商射の共通係数商上の線形射。 -/
def deltaDivisionFiniteNormalizedTowerLinearMap (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
    DeltaDivisionFiniteNormalizedQuotient D d a u n →ₗ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedQuotient D d a u m := by
  letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
  letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
  exact (deltaDivisionFiniteNormalizedTowerAlgHom D d a u h).toLinearMap

/-- 全段への標準射は共通係数商上の具体的代数射。 -/
def deltaDivisionFiniteNormalizedDirectLimitOfAlgHom (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    DeltaDivisionFiniteNormalizedQuotient D d a u N →ₐ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  exact { deltaDivisionFiniteNormalizedDirectLimitOf D d a u N with
    commutes' := fun b =>
      (RingHom.congr_fun
        (deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp D d a u N) b).symm }

/-- 各段から全段への標準線形射。 -/
def deltaDivisionFiniteNormalizedDirectLimitOfLinearMap (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    DeltaDivisionFiniteNormalizedQuotient D d a u N →ₗ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  exact (deltaDivisionFiniteNormalizedDirectLimitOfAlgHom D d a u N).toLinearMap

/-- 共通係数商上の線形射も、実際の環直系と同じ直系条件を満たす。 -/
theorem deltaDivisionFiniteNormalizedLinearDirectedSystem (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := fun N => deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    DirectedSystem (fun N : ℕ => DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (fun _ _ h => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) := by
  let := fun N => deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  exact deltaDivisionFiniteNormalizedDirectedSystem D d a u

end SerrePositivity.BhattScholze
