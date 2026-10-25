module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialIdeal

/-! # 具体的階乗部分環と正次数イデアルの関手的な写像

Mathlibの局所化写像を用い、基底と階乗生成元上の式を保つ実環射を構成する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}
local notation "Aₚ" => Localization.Away (p : A)
local notation "Bₚ" => Localization.Away (p : B)

/-- 基底環射を、既存IsLocalization.mapによってp局所化へ延長する。 -/
def pDivisionFactorialAwayMap (p : ℕ) (f : A →+* B) :
    Localization.Away (p : A) →+* Localization.Away (p : B) :=
  IsLocalization.map (M := Submonoid.powers (p : A)) (T := Submonoid.powers (p : B))
    (Localization.Away (p : B)) f (by
    rintro x ⟨n, rfl⟩
    use n
    simp only [map_pow, map_natCast])

omit [Fact p.Prime] in
/-- p局所化間の実写像は元の基底環射を延長する。 -/
theorem pDivisionFactorialAwayMap_coeff (f : A →+* B) (a : A) :
    pDivisionFactorialAwayMap p f (algebraMap A Aₚ a) = algebraMap B Bₚ (f a) :=
  IsLocalization.map_eq _ _

/-- 源のp局所性の下で、実局所化写像は正規化した階乗分母を保つ。 -/
theorem pDivisionFactorialAwayMap_value (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) (s : σ) (n : ℕ) :
    pDivisionFactorialAwayMap p f (pDivisionFactorialValue p y s n) =
      pDivisionFactorialValue p (fun s ↦ f (y s)) s n := by
  have hu := DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)
  rw [pDivisionFactorialValue, map_mul, hu.map_ringInverse, map_natCast,
    map_pow, pDivisionFactorialAwayMap_coeff]
  rfl

/-- 局所化写像は、具体的な階乗生成部分環を対応する部分環へ写す。 -/
theorem pDivisionFactorialAwayMap_mem (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) (t : Aₚ) (ht : t ∈ pDivisionFactorialSubring p y) :
    pDivisionFactorialAwayMap p f t ∈ pDivisionFactorialSubring p (fun s ↦ f (y s)) := by
  have hle : pDivisionFactorialSubring p y ≤
      (pDivisionFactorialSubring p (fun s ↦ f (y s))).comap (pDivisionFactorialAwayMap p f) := by
    apply Subring.closure_le.mpr
    rintro x (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · change pDivisionFactorialAwayMap p f (algebraMap A Aₚ a) ∈
        pDivisionFactorialSubring p (fun s ↦ f (y s))
      rw [pDivisionFactorialAwayMap_coeff]
      exact pDivisionFactorialSubring_coeff_mem _ _
    · change pDivisionFactorialAwayMap p f (pDivisionFactorialValue p y s n) ∈
        pDivisionFactorialSubring p (fun s ↦ f (y s))
      rw [pDivisionFactorialAwayMap_value hlocal]
      exact pDivisionFactorialSubring_value_mem _ s n
  exact hle ht

/-- 基底環射が誘導する、具体的階乗生成部分環間の実環射。 -/
def pDivisionFactorialMap (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) :
    pDivisionFactorialSubring p y →+* pDivisionFactorialSubring p (fun s ↦ f (y s)) :=
  ((pDivisionFactorialAwayMap p f).comp (pDivisionFactorialSubring p y).subtype).codRestrict _
    (fun t ↦ pDivisionFactorialAwayMap_mem hlocal f y t t.property)

/-- 誘導された実環射は、元のAからの基底標準射と可換。 -/
theorem pDivisionFactorialMap_comp_base (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) :
    (pDivisionFactorialMap hlocal f y).comp (pDivisionFactorialBase p y) =
      (pDivisionFactorialBase p (fun s ↦ f (y s))).comp f := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact pDivisionFactorialAwayMap_coeff f a

/-- 誘導された実環射は、各階乗生成元を対応する標準生成元へ送る。 -/
theorem pDivisionFactorialMap_value (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) (s : σ) (n : ℕ) :
    pDivisionFactorialMap hlocal f y
      ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      ⟨pDivisionFactorialValue p (fun s ↦ f (y s)) s n,
        pDivisionFactorialSubring_value_mem (fun s ↦ f (y s)) s n⟩ := by
  apply Subtype.ext
  exact pDivisionFactorialAwayMap_value hlocal f y s n

/-- 正次数階乗イデアルの像は、対応する標的の正次数階乗イデアルに含まれる。 -/
theorem pDivisionFactorialMap_ideal_le (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) :
    (pDivisionFactorialIdeal p y).map (pDivisionFactorialMap hlocal f y) ≤
      pDivisionFactorialIdeal p (fun s ↦ f (y s)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro t ⟨⟨s, n⟩, rfl⟩
  change pDivisionFactorialMap hlocal f y _ ∈
    pDivisionFactorialIdeal p (fun s ↦ f (y s))
  rw [pDivisionFactorialMap_value]
  exact Ideal.subset_span (Set.mem_range_self (s, n))

end SerrePositivity.BhattScholze
