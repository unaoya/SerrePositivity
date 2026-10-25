module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteNormalizedBaseFlat
public import Mathlib.Algebra.Colimit.DirectLimit

/-! # 標準有限正規化商から構成した具体的全段環 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 標準有限商射の直系条件。既存の合成・恒等式を再利用する。 -/
instance deltaDivisionFiniteNormalizedDirectedSystem (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    DirectedSystem (fun N : ℕ => DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (fun _ _ h => deltaDivisionFiniteNormalizedTowerMap D d a u h) where
  map_self {i} x := by
    change deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_refl i) x = x
    rw [deltaDivisionFiniteNormalizedTowerMap_self]
    rfl
  map_map {k j i} hij hjk x :=
    RingHom.congr_fun (deltaDivisionFiniteNormalizedTowerMap_comp D d a u hij hjk) x

/-- BS固有の全段環。直極限一般論はMathlibの有向環直極限を使う。 -/
abbrev DeltaDivisionFiniteNormalizedDirectLimit (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :=
  DirectLimit (fun N : ℕ => DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (fun _ _ h => deltaDivisionFiniteNormalizedTowerMap D d a u h)

/-- 各有限段から全段環への標準環射。 -/
def deltaDivisionFiniteNormalizedDirectLimitOf (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    DeltaDivisionFiniteNormalizedQuotient D d a u N →+*
      DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  DirectLimit.Ring.of _ _ N

/-- 全段環への標準射は任意二段間の塔射と可換。 -/
theorem deltaDivisionFiniteNormalizedDirectLimitOf_compatible (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m)
    (x : DeltaDivisionFiniteNormalizedQuotient D d a u n) :
    deltaDivisionFiniteNormalizedDirectLimitOf D d a u m
      (deltaDivisionFiniteNormalizedTowerMap D d a u h x) =
        deltaDivisionFiniteNormalizedDirectLimitOf D d a u n x :=
  DirectLimit.Ring.of_f h x

/-- 各有限段から全段環への標準射は単射。 -/
theorem deltaDivisionFiniteNormalizedDirectLimitOf_injective (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Function.Injective (deltaDivisionFiniteNormalizedDirectLimitOf D d a u N) :=
  DirectLimit.mk_injective
    (fun _ _ h => deltaDivisionFiniteNormalizedTowerMap D d a u h)
    (fun _ _ h => deltaDivisionFiniteNormalizedTowerMap_injective D d a u h) N

/-- 全段環の任意元は具体的有限商のある段の標準像。 -/
theorem deltaDivisionFiniteNormalizedDirectLimit_exists_stage (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (y : DeltaDivisionFiniteNormalizedDirectLimit D d a u) :
    ∃ N, ∃ x : DeltaDivisionFiniteNormalizedQuotient D d a u N,
      deltaDivisionFiniteNormalizedDirectLimitOf D d a u N x = y := by
  obtain ⟨N, x, hx⟩ := DirectLimit.exists_eq_mk
    (fun _ _ h => deltaDivisionFiniteNormalizedTowerMap D d a u h) y
  exact ⟨N, x, hx.symm⟩

/-- 適切な共通係数商A/(p,d,a_s)から全段環への具体的射。 -/
def deltaDivisionFiniteNormalizedDirectLimitBaseMap (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (deltaDivisionFiniteNormalizedDirectLimitOf D d a u 0).comp
    (deltaDivisionFiniteNormalizedInitialBaseMap D d a u)

/-- 全段係数射は、どの有限段の係数射とも整合する。 -/
theorem deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u =
      (deltaDivisionFiniteNormalizedDirectLimitOf D d a u N).comp
        (deltaDivisionFiniteNormalizedBaseMap D d a u N) := by
  apply RingHom.ext
  intro b
  exact (deltaDivisionFiniteNormalizedDirectLimitOf_compatible
    D d a u (Nat.zero_le N) (deltaDivisionFiniteNormalizedInitialBaseMap D d a u b)).symm

/-- 全段係数射は、基底係数の任意有限段での標準商像に一致する。 -/
theorem deltaDivisionFiniteNormalizedDirectLimitBaseMap_mk (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (b : A) :
    deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) =
      deltaDivisionFiniteNormalizedDirectLimitOf D d a u N
        (Ideal.Quotient.mk _ (MvPolynomial.C b)) := by
  rw [deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp D d a u N,
    RingHom.comp_apply, deltaDivisionFiniteNormalizedBaseMap_mk]

/-- 適切な共通係数商から全段環への射も単射。 -/
theorem deltaDivisionFiniteNormalizedDirectLimitBaseMap_injective (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    Function.Injective (deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u) := by
  rw [deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp D d a u 0]
  exact (deltaDivisionFiniteNormalizedDirectLimitOf_injective D d a u 0).comp
    (deltaDivisionFiniteNormalizedBaseMap_injective D d a u 0)

end SerrePositivity.BhattScholze
