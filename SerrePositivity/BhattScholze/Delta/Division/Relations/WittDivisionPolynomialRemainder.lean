module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.WittDivisionTriangular
public import Mathlib.Algebra.MvPolynomial.Variables

/-! # Witt除算の下位剰余多項式

整数係数の有限多項式を固定し、除数係数とp乗変数へ置換する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Witt積の既存剰余多項式を有限変数へ制限できる。 -/
theorem exists_wittDivisionLowerIntegerPolynomial (n : ℕ) :
    ∃ P : MvPolynomial (Fin 2 × Fin (n + 1)) ℤ,
      MvPolynomial.rename (fun z => (z.1, z.2.val)) P = WittVector.polyOfInterest p n := by
  let ι : Fin 2 × Fin (n + 1) → Fin 2 × ℕ := fun z => (z.1, z.2.val)
  have hi : Function.Injective ι := by
    intro x y h
    exact Prod.ext (congrArg (fun z : Fin 2 × ℕ => z.1) h)
      (Fin.ext (congrArg (fun z : Fin 2 × ℕ => z.2) h))
  apply MvPolynomial.exists_rename_eq_of_vars_subset_range _ ι hi
  intro z hz
  have h := (WittVector.polyOfInterest_vars p n) hz
  exact ⟨(z.1, ⟨z.2, Finset.mem_range.mp (Finset.mem_product.mp h).2⟩), rfl⟩

/-- 除算剰余構成に使う、固定された有限整数多項式。 -/
def wittDivisionLowerIntegerPolynomial (p : ℕ) [Fact p.Prime] (n : ℕ) :
    MvPolynomial (Fin 2 × Fin (n + 1)) ℤ :=
  Classical.choose (exists_wittDivisionLowerIntegerPolynomial (p := p) n)

/-- 有限整数多項式の標準包含は既存Witt剰余多項式。 -/
theorem wittDivisionLowerIntegerPolynomial_rename (n : ℕ) :
    MvPolynomial.rename (fun z => (z.1, z.2.val)) (wittDivisionLowerIntegerPolynomial p n) =
      WittVector.polyOfInterest p n :=
  Classical.choose_spec (exists_wittDivisionLowerIntegerPolynomial (p := p) n)

/-- 固定除数の全段Witt三角形公式に使う、下位座標だけの実際の多項式。 -/
def wittDivisionRemainderPolynomial (x : WittVector p R) (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.C (x.coeff (n + 2)) *
      (MvPolynomial.X ⟨0, Nat.zero_lt_succ n⟩ ^ p) ^ (p ^ (n + 1)) +
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun z : Fin 2 × Fin (n + 1) => if z.1 = 0 then MvPolynomial.C (x.coeff (z.2.val + 1))
        else MvPolynomial.X z.2 ^ p) (wittDivisionLowerIntegerPolynomial p n)

/-- pを消す係数環で、除算剰余は構成した下位多項式の評価として表せる。 -/
theorem wittDivisionRemainderPolynomial_spec (hp : (p : R) = 0)
    (x : WittVector p R) (hx : x.coeff 0 = 0) (n : ℕ) (y : WittVector p R) :
    (x * y).coeff (n + 2) = x.coeff 1 ^ (p ^ (n + 1)) * y.coeff (n + 1) ^ p +
      MvPolynomial.eval₂Hom (RingHom.id R) (fun i : Fin (n + 1) => y.coeff i.val)
        (wittDivisionRemainderPolynomial x n) := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h => let := h; exact Subsingleton.elim _ _
  | inr h =>
      let := h
      let : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      let z : WittVector p R := WittVector.mk p (fun i => x.coeff (i + 1))
      let e := MvPolynomial.eval₂Hom (RingHom.id R) (fun i : Fin (n + 1) => y.coeff i.val)
      let g : Fin 2 × Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := fun b =>
        if b.1 = 0 then MvPolynomial.C (x.coeff (b.2.val + 1)) else MvPolynomial.X b.2 ^ p
      let t : Fin 2 × Fin (n + 1) → R := fun b =>
        if b.1 = 0 then x.coeff (b.2.val + 1) else y.coeff b.2.val ^ p
      have hm : e.comp (MvPolynomial.eval₂Hom (Int.castRingHom _) g) =
          MvPolynomial.eval₂Hom (Int.castRingHom R) t := by
        rw [MvPolynomial.comp_eval₂Hom]
        congr 1
        · exact Subsingleton.elim _ _
        · funext b
          by_cases hb : b.1 = 0 <;> simp [g, t, e, hb]
      have hpe : WittVector.peval (WittVector.polyOfInterest p n)
          ![fun i => z.coeff i, fun i => (WittVector.frobenius y).coeff i] =
          MvPolynomial.eval₂Hom (Int.castRingHom R) t (wittDivisionLowerIntegerPolynomial p n) := by
        rw [← wittDivisionLowerIntegerPolynomial_rename]
        simp only [WittVector.peval, MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_rename]
        apply MvPolynomial.eval₂Hom_congr (Subsingleton.elim _ _) ?_ rfl
        funext b
        rcases b with ⟨b, i⟩
        fin_cases b <;> simp [t, z, WittVector.coeff_frobenius_charP]
      have heval : e (wittDivisionRemainderPolynomial x n) =
          x.coeff (n + 2) * (y.coeff 0 ^ p) ^ (p ^ (n + 1)) +
            WittVector.peval (WittVector.polyOfInterest p n)
              ![fun i => z.coeff i, fun i => (WittVector.frobenius y).coeff i] := by
        rw [wittDivisionRemainderPolynomial, map_add, map_mul, map_pow, map_pow]
        simp only [e, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
        rw [hpe]
        exact congrArg (fun v => x.coeff (n + 2) * (y.coeff 0 ^ p) ^ (p ^ (n + 1)) + v)
          (RingHom.congr_fun hm (wittDivisionLowerIntegerPolynomial p n))
      have hV : WittVector.verschiebung z = x := by
        ext i
        cases i with
        | zero => simpa only [WittVector.verschiebung_coeff_zero] using hx.symm
        | succ i => simp only [WittVector.verschiebung_coeff_succ, z, WittVector.coeff_mk]
      have he : (x * y).coeff (n + 2) = (z * WittVector.frobenius y).coeff (n + 1) := by
        calc
          _ = (WittVector.verschiebung z * y).coeff (n + 2) := by rw [hV]
          _ = (WittVector.verschiebung (z * WittVector.frobenius y)).coeff (n + 2) := by
            rw [WittVector.verschiebung_mul_frobenius]
          _ = _ := WittVector.verschiebung_coeff_succ _ _
      have hs := WittVector.peval_polyOfInterest' p n z (WittVector.frobenius y)
      simp only [z, WittVector.coeff_mk, WittVector.coeff_frobenius_charP] at hs
      change _ = _ + e (wittDivisionRemainderPolynomial x n)
      rw [he, heval]
      simp only [z, WittVector.coeff_mk, WittVector.coeff_frobenius_charP] at *
      linear_combination -hs

/-- 剰余多項式は係数環射と両立する。p消滅・非零性の仮定は不要。 -/
theorem wittDivisionRemainderPolynomial_map {S : Type v} [CommRing S]
    (f : R →+* S) (x : WittVector p R) (n : ℕ) :
    MvPolynomial.map f (wittDivisionRemainderPolynomial x n) =
      wittDivisionRemainderPolynomial (WittVector.map f x) n := by
  simp only [wittDivisionRemainderPolynomial, map_add, map_mul, map_pow,
    MvPolynomial.map_C, MvPolynomial.map_X, WittVector.map_coeff]
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (MvPolynomial.map f).comp (Int.castRingHom (MvPolynomial (Fin (n + 1)) R)) =
      Int.castRingHom (MvPolynomial (Fin (n + 1)) S) := Subsingleton.elim _ _
  rw [hc]
  congr 1
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext b
  by_cases hb : b.1 = 0 <;> simp [hb]

/-- 実際の下位多項式評価を係数とする、全段のモニックWitt積方程式。 -/
theorem wittDivisionRemainderPolynomial_monic_equation (hp : (p : R) = 0)
    (x : WittVector p R) (hx : x.coeff 0 = 0) (u : Rˣ) (hu : (u : R) = x.coeff 1)
    (n : ℕ) (y : WittVector p R) (c : R) :
    let a := ((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) *
      (c - MvPolynomial.eval₂Hom (RingHom.id R) (fun i : Fin (n + 1) => y.coeff i.val)
        (wittDivisionRemainderPolynomial x n))
    (Polynomial.X ^ p - Polynomial.C a).Monic ∧
      ((x * y).coeff (n + 2) = c ↔
        Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C a) (y.coeff (n + 1))) := by
  dsimp only
  constructor
  · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  · rw [wittDivisionRemainderPolynomial_spec hp x hx n y, ← hu]
    change _ ↔ Polynomial.eval _ _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero]
    constructor
    · intro h
      have he : (u : R) ^ (p ^ (n + 1)) * y.coeff (n + 1) ^ p =
          c - MvPolynomial.eval₂Hom (RingHom.id R) (fun i : Fin (n + 1) => y.coeff i.val)
            (wittDivisionRemainderPolynomial x n) := by
        rw [← h]
        ring
      calc
        y.coeff (n + 1) ^ p =
            (((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) * (u : R) ^ (p ^ (n + 1))) *
              y.coeff (n + 1) ^ p := by rw [← mul_pow]; simp
        _ = _ := by rw [mul_assoc, he]
    · intro h
      rw [h, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
      ring

end SerrePositivity.BhattScholze
