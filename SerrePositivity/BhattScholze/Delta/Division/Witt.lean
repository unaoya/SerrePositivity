module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWitt
public import SerrePositivity.BhattScholze.Delta.Division.Relations
public import Mathlib.RingTheory.WittVector.MulCoeff
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.MvPolynomial.Variables
public import SerrePositivity.BhattScholze.Delta.Division.Residue
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul

/-!
# Witt 座標による δ 関係の正規化

## 概要
Witt 除算の下位剰余多項式と零定数係数の Witt 除数の三角形表示、δ 除算関係式と切り詰め Witt 積方程式・全段 Witt モニック方程式の対応、Witt 根関係元とその自然性、下位関係イデアル上での Witt 根関係元への置換と正則性、逆 Witt 座標による有限関係イデアルの正規化と正規化モニック商との同型、正規化関係イデアルの初期有限変数による表示と後続式。
BS 著者版 Remark 2.14 の Witt 座標を、Remark 7.15 の包に使う δ 除算関係式に適用する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/JetKoszul`、`Andre/Envelope/Normalized`。
-/

universe u v w

/-! ## 全有限δ除算関係式と切り詰めWitt積方程式の対応

任意通常射の下で比較し、終域のδ構造は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionWittJetRelations

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 通常除算関係式の有限δjet消滅は、切り詰めWitt積方程式と同値。 -/
theorem deltaDivision_jets_zero_iff_witt_truncate_equation (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (d x a : A) (N : ℕ) :
    (∀ i ≤ N, q (D.delta^[i] (d * x - a)) = 0) ↔
      WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D d)) *
        WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D x)) =
          WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D a)) := by
  rw [deltaWittGhostVector_jets_zero_iff_truncate_map_zero D hp hg]
  let f := (WittVector.truncate (N + 1)).comp ((WittVector.map q).comp (deltaWittGhostRingHom D hg))
  change f (d * x - a) = 0 ↔ f d * f x = f a
  rw [map_sub, map_mul, sub_eq_zero]

/-- 任意族の有限反復除算関係式も、同じ深さのWitt積方程式族と同値。 -/
theorem deltaDivision_family_jets_zero_iff_witt_truncate_equations {σ : Type w}
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (d : A) (x a : σ → A) (N : ℕ) :
    (∀ s i, i ≤ N → q (D.delta^[i] (d * x s - a s)) = 0) ↔
      (∀ s, WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D d)) *
        WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D (x s))) =
          WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D (a s)))) := by
  constructor
  · intro h s
    exact (deltaDivision_jets_zero_iff_witt_truncate_equation D hp hg q d (x s) (a s) N).mp (h s)
  · intro h s
    exact (deltaDivision_jets_zero_iff_witt_truncate_equation D hp hg q d (x s) (a s) N).mpr (h s)

/-- 相対自由δ環の実際の全有限反復関係式とWitt積方程式族の比較。 -/
theorem deltaDivisionIteratedRelations_zero_iff_witt_truncate_equations {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (hp : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) (N : ℕ) :
    (∀ s i, i ≤ N → q (deltaDivisionIteratedRelation D d a s i) = 0) ↔
      (∀ s, WittVector.truncate (N + 1)
          (WittVector.map q (deltaWittGhostVector (relativeFreeDeltaStructure σ D)
            (MvPolynomial.C d))) *
        WittVector.truncate (N + 1)
          (WittVector.map q (deltaWittGhostVector (relativeFreeDeltaStructure σ D)
            (MvPolynomial.X (s, 0)))) =
        WittVector.truncate (N + 1)
          (WittVector.map q (deltaWittGhostVector (relativeFreeDeltaStructure σ D)
            (MvPolynomial.C (a s))))) := by
  exact deltaDivision_family_jets_zero_iff_witt_truncate_equations
    (relativeFreeDeltaStructure σ D) hp hg q (MvPolynomial.C d)
    (fun s => MvPolynomial.X (s, 0)) (fun s => MvPolynomial.C (a s)) N

end SerrePositivity.BhattScholze

end DeltaDivisionWittJetRelations

/-! ## 零定数係数のWitt除数の全段三角形表示

Verschiebungで一段下げて既存のWitt積係数公式を使う。
-/

@[expose] public noncomputable section WittDivisionTriangular

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 零定数係数の除数の第n+2積係数は、次の変数のp乗と下位係数だけで表される。 -/
theorem wittDivision_exists_triangular_remainder
    (hp : (p : R) = 0) (x : WittVector p R) (hx : x.coeff 0 = 0) (n : ℕ) :
    ∃ r : (Fin (n + 1) → R) → R, ∀ y : WittVector p R,
      (x * y).coeff (n + 2) =
        x.coeff 1 ^ (p ^ (n + 1)) * y.coeff (n + 1) ^ p +
          r (WittVector.truncateFun (n + 1) y) := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
      let := h
      exact ⟨fun _ => 0, fun _ => Subsingleton.elim _ _⟩
  | inr h =>
      let := h
      let : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      let z : WittVector p R := WittVector.mk p (fun i => x.coeff (i + 1))
      have hV : WittVector.verschiebung z = x := by
        ext i
        cases i with
        | zero => simpa only [WittVector.verschiebung_coeff_zero] using hx.symm
        | succ i => simp only [WittVector.verschiebung_coeff_succ, z, WittVector.coeff_mk]
      let r : (Fin (n + 1) → R) → R := fun v =>
        x.coeff (n + 2) * (v ⟨0, Nat.zero_lt_succ n⟩ ^ p) ^ (p ^ (n + 1)) +
          WittVector.nthRemainder p n (WittVector.truncateFun (n + 1) z) (fun i => v i ^ p)
      refine ⟨r, ?_⟩
      intro y
      have he : (x * y).coeff (n + 2) = (z * WittVector.frobenius y).coeff (n + 1) := by
        calc
          _ = (WittVector.verschiebung z * y).coeff (n + 2) := by rw [hV]
          _ = (WittVector.verschiebung (z * WittVector.frobenius y)).coeff (n + 2) := by
            rw [WittVector.verschiebung_mul_frobenius]
          _ = _ := WittVector.verschiebung_coeff_succ _ _
      rw [he, WittVector.nthRemainder_spec]
      simp only [z, WittVector.coeff_mk, WittVector.coeff_frobenius_charP]
      have ht : WittVector.truncateFun (n + 1) (WittVector.frobenius y) =
          fun i => (WittVector.truncateFun (n + 1) y i) ^ p := by
        funext i
        exact WittVector.coeff_frobenius_charP p y i.val
      rw [ht]
      simp only [r, z, WittVector.truncateFun, TruncatedWittVector.mk,
        WittVector.coeff_mk]
      ring

/-- 単元第1係数のWitt除数について、全段の積係数方程式はモニックp乗方程式。 -/
theorem wittDivision_exists_monic_equation
    (hp : (p : R) = 0) (x : WittVector p R) (hx : x.coeff 0 = 0)
    (u : Rˣ) (hu : (u : R) = x.coeff 1) (n : ℕ) :
    ∃ r : (Fin (n + 1) → R) → R, ∀ (y : WittVector p R) (c : R),
      (Polynomial.X ^ p - Polynomial.C
        (((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) *
          (c - r (WittVector.truncateFun (n + 1) y)))).Monic ∧
      ((x * y).coeff (n + 2) = c ↔
        Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C
          (((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) *
            (c - r (WittVector.truncateFun (n + 1) y)))) (y.coeff (n + 1))) := by
  obtain ⟨r, hr⟩ := wittDivision_exists_triangular_remainder hp x hx n
  refine ⟨r, fun y c => ?_⟩
  constructor
  · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  · rw [hr y, ← hu]
    change _ ↔ Polynomial.eval _ _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero]
    constructor
    · intro h
      have he : (u : R) ^ (p ^ (n + 1)) * y.coeff (n + 1) ^ p =
          c - r (WittVector.truncateFun (n + 1) y) := by
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

end WittDivisionTriangular

/-! ## 実際のδ除算関係式からの全段Wittモニック方程式

有限δjet消滅を積係数等式へ移し、既存全段Witt三角形公式を使う。
-/

@[expose] public noncomputable section DeltaDivisionWittMonicRelations

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 有限δ除算関係式を消す通常射の下で、対応する全Witt積係数は一致する。 -/
theorem deltaDivision_witt_mul_coeff_eq_of_jets_zero (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (d x a : A) (N i : ℕ) (hi : i ≤ N)
    (hjets : ∀ j ≤ N, q (D.delta^[j] (d * x - a)) = 0) :
    (WittVector.map q (deltaWittGhostVector D d) *
      WittVector.map q (deltaWittGhostVector D x)).coeff i =
      q ((deltaWittGhostVector D a).coeff i) := by
  have he := (deltaDivision_jets_zero_iff_witt_truncate_equation D hp hg q d x a N).mp hjets
  rw [← map_mul] at he
  have hc := congrArg (fun w : TruncatedWittVector p (N + 1) B => w.coeff ⟨i, by omega⟩) he
  simpa only [WittVector.coeff_truncate, WittVector.map_coeff] using hc

/-- 除数を固定すると、全段のδ関係式から下位Witt座標だけを係数とするモニック式を得る。 -/
theorem deltaDivision_exists_witt_monic_relations (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (hqp : q (p : A) = 0) (d : A) (hqd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) (n : ℕ) :
    ∃ r : (Fin (n + 1) → B) → B, ∀ x a : A,
      (∀ i ≤ n + 2, q (D.delta^[i] (d * x - a)) = 0) →
      let c := ((u⁻¹ : Bˣ) : B) ^ (p ^ (n + 1)) *
        (q ((deltaWittGhostVector D a).coeff (n + 2)) -
          r (WittVector.truncateFun (n + 1) (WittVector.map q (deltaWittGhostVector D x))))
      (Polynomial.X ^ p - Polynomial.C c).Monic ∧
        Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C c)
          (q ((deltaWittGhostVector D x).coeff (n + 1))) := by
  have hpB : (p : B) = 0 := by simpa only [map_natCast] using hqp
  let w := WittVector.map q (deltaWittGhostVector D d)
  have hw : w.coeff 0 = 0 := by
    simp only [w, WittVector.map_coeff, deltaWittGhostVector_coeff_zero, hqd]
  have hu' : (u : B) = w.coeff 1 := by
    simpa only [w, WittVector.map_coeff, deltaWittGhostVector_coeff_one D hp] using hu
  obtain ⟨r, hr⟩ := wittDivision_exists_monic_equation hpB w hw u hu' n
  refine ⟨r, fun x a hjets => ?_⟩
  have hc := deltaDivision_witt_mul_coeff_eq_of_jets_zero D hp hg q d x a
    (n + 2) (n + 2) le_rfl hjets
  have he := hr (WittVector.map q (deltaWittGhostVector D x))
    (q ((deltaWittGhostVector D a).coeff (n + 2)))
  have hroot := he.2.mp hc
  exact ⟨he.1, by simpa only [WittVector.map_coeff] using hroot⟩

/-- distinguished除数は全段で同じ単元係数を供給する。 -/
theorem exists_deltaDivision_witt_monic_relations_of_distinguished (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (hqp : q (p : A) = 0) (d : A) (hqd : q d = 0)
    (hd : D.IsDistinguished d) :
    ∃ u : Bˣ, (u : B) = q (D.delta d) ∧ ∀ n : ℕ,
      ∃ r : (Fin (n + 1) → B) → B, ∀ x a : A,
        (∀ i ≤ n + 2, q (D.delta^[i] (d * x - a)) = 0) →
        let c := ((u⁻¹ : Bˣ) : B) ^ (p ^ (n + 1)) *
          (q ((deltaWittGhostVector D a).coeff (n + 2)) -
            r (WittVector.truncateFun (n + 1) (WittVector.map q (deltaWittGhostVector D x))))
        (Polynomial.X ^ p - Polynomial.C c).Monic ∧
          Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C c)
            (q ((deltaWittGhostVector D x).coeff (n + 1))) := by
  obtain ⟨u, hu⟩ := hd.map q
  exact ⟨u, hu, fun n => deltaDivision_exists_witt_monic_relations D hp hg q hqp d hqd u hu n⟩

end SerrePositivity.BhattScholze

end DeltaDivisionWittMonicRelations

/-! ## Witt除算の下位剰余多項式

整数係数の有限多項式を固定し、除数係数とp乗変数へ置換する。
-/

@[expose] public noncomputable section WittDivisionPolynomialRemainder

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

end WittDivisionPolynomialRemainder

/-! ## 実際のδ除算関係式の次段と具体的モニック多項式の根条件

下位関係式を仮定して、次の関係式の消滅を双方向に比較する。
-/

@[expose] public noncomputable section DeltaDivisionWittPolynomialRelations

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 下位Witt座標の実際の剰余多項式評価を使う、除算のモニック根多項式。 -/
def deltaDivisionWittRootPolynomial (D : DeltaStructure p A) (q : A →+* B)
    (d x a : A) (u : Bˣ) (n : ℕ) : Polynomial B :=
  Polynomial.X ^ p - Polynomial.C
    (((u⁻¹ : Bˣ) : B) ^ (p ^ (n + 1)) *
      (q ((deltaWittGhostVector D a).coeff (n + 2)) -
        MvPolynomial.eval₂Hom (RingHom.id B)
          (fun i : Fin (n + 1) => q ((deltaWittGhostVector D x).coeff i.val))
          (wittDivisionRemainderPolynomial (WittVector.map q (deltaWittGhostVector D d)) n)))

/-- この具体的な根多項式は零環を含めてモニック。 -/
theorem deltaDivisionWittRootPolynomial_monic (D : DeltaStructure p A) (q : A →+* B)
    (d x a : A) (u : Bˣ) (n : ℕ) :
    (deltaDivisionWittRootPolynomial D q d x a u n).Monic :=
  Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero

/-- 下位δ関係式消滅下で、次のδ関係式は次のWitt積係数等式と同値。 -/
theorem deltaDivision_next_jet_zero_iff_witt_mul_coeff_eq (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (d x a : A) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, q (D.delta^[i] (d * x - a)) = 0) :
    q (D.delta^[n + 2] (d * x - a)) = 0 ↔
      (WittVector.map q (deltaWittGhostVector D d) *
        WittVector.map q (deltaWittGhostVector D x)).coeff (n + 2) =
          q ((deltaWittGhostVector D a).coeff (n + 2)) := by
  have hfull : q (D.delta^[n + 2] (d * x - a)) = 0 ↔
      ∀ i ≤ n + 2, q (D.delta^[i] (d * x - a)) = 0 := by
    constructor
    · intro h i hi
      by_cases he : i = n + 2
      · simpa only [he] using h
      · exact hlower i (by omega)
    · intro h
      exact h (n + 2) le_rfl
  rw [hfull, deltaDivision_jets_zero_iff_witt_truncate_equation D hp hg]
  rw [← map_mul]
  constructor
  · intro h
    have hc := congrArg (fun w : TruncatedWittVector p (n + 2 + 1) B =>
      w.coeff ⟨n + 2, by omega⟩) h
    simpa only [WittVector.coeff_truncate, WittVector.map_coeff] using hc
  · intro h
    apply TruncatedWittVector.ext
    intro i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.map_coeff]
    by_cases he : i.val = n + 2
    · simpa only [he] using h
    · exact deltaDivision_witt_mul_coeff_eq_of_jets_zero D hp hg q d x a
        (n + 1) i.val (by have := i.isLt; omega) hlower

/-- 下位δ関係式消滅下で、次の関係式の消滅は具体的モニック根条件と同値。 -/
theorem deltaDivision_next_jet_zero_iff_witt_polynomial_root (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (hqp : q (p : A) = 0) (d x a : A) (hqd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, q (D.delta^[i] (d * x - a)) = 0) :
    q (D.delta^[n + 2] (d * x - a)) = 0 ↔
      Polynomial.IsRoot (deltaDivisionWittRootPolynomial D q d x a u n)
        (q ((deltaWittGhostVector D x).coeff (n + 1))) := by
  have hpB : (p : B) = 0 := by simpa only [map_natCast] using hqp
  let w := WittVector.map q (deltaWittGhostVector D d)
  have hw : w.coeff 0 = 0 := by
    simp only [w, WittVector.map_coeff, deltaWittGhostVector_coeff_zero, hqd]
  have hu' : (u : B) = w.coeff 1 := by
    simpa only [w, WittVector.map_coeff, deltaWittGhostVector_coeff_one D hp] using hu
  have he := wittDivisionRemainderPolynomial_monic_equation hpB w hw u hu' n
    (WittVector.map q (deltaWittGhostVector D x)) (q ((deltaWittGhostVector D a).coeff (n + 2)))
  have hs := (deltaDivision_next_jet_zero_iff_witt_mul_coeff_eq D hp hg q d x a n hlower).trans he.2
  simpa only [deltaDivisionWittRootPolynomial, WittVector.map_coeff] using hs

end SerrePositivity.BhattScholze

end DeltaDivisionWittPolynomialRelations

/-! ## 源のWitt根関係元と通常射での自然性

源の指定単元を使い、根多項式の評価を実際の環元として固定する。
-/

@[expose] public noncomputable section DeltaDivisionWittRelationElement

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 源のWitt座標で評価した、次段モニック根多項式の具体的な関係元。 -/
def deltaDivisionWittRelationElement (D : DeltaStructure p A) (d x a : A) (u : Aˣ) (n : ℕ) : A :=
  Polynomial.eval ((deltaWittGhostVector D x).coeff (n + 1))
    (deltaDivisionWittRootPolynomial D (RingHom.id A) d x a u n)

/-- 源の根関係元の像は、係数射の先の根多項式評価に一致する。 -/
theorem deltaDivisionWittRelationElement_map (D : DeltaStructure p A) (q : A →+* B)
    (d x a : A) (u : Aˣ) (n : ℕ) :
    q (deltaDivisionWittRelationElement D d x a u n) =
      Polynomial.eval (q ((deltaWittGhostVector D x).coeff (n + 1)))
        (deltaDivisionWittRootPolynomial D q d x a (u.map q) n) := by
  simp only [deltaDivisionWittRelationElement, deltaDivisionWittRootPolynomial,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    RingHom.id_apply, WittVector.map_id]
  simp only [map_sub, map_pow, map_mul, Units.coe_map_inv]
  rw [MvPolynomial.map_eval₂Hom, ← wittDivisionRemainderPolynomial_map]
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

/-- 下位δjet消滅下で、次段δ関係式消滅は源の根関係元の像の消滅と同値。 -/
theorem deltaDivision_next_jet_zero_iff_witt_relation_map_zero (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (hqp : q (p : A) = 0) (d x a : A) (hqd : q d = 0)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, q (D.delta^[i] (d * x - a)) = 0) :
    q (D.delta^[n + 2] (d * x - a)) = 0 ↔ q (deltaDivisionWittRelationElement D d x a u n) = 0 := by
  rw [deltaDivisionWittRelationElement_map]
  have hu' : ((u.map q : Bˣ) : B) = q (D.delta d) := by
    change q (u : A) = _
    rw [hu]
  have he := deltaDivision_next_jet_zero_iff_witt_polynomial_root D hp hg q hqp d x a hqd
    (u.map q) hu' n hlower
  rw [Polynomial.IsRoot.def] at he
  exact he

end SerrePositivity.BhattScholze

end DeltaDivisionWittRelationElement

/-! ## 下位関係イデアル上の次段δ生成元のWitt根関係元への置換

商射での消滅比較により、任意の下位イデアル上で正確なイデアル等式を示す。
-/

@[expose] public noncomputable section DeltaDivisionWittRelationIdeal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p,dと下位δ関係式を含むイデアルでは、次段生成元とWitt根関係元の所属は同値。 -/
theorem deltaDivision_next_jet_mem_iff_witt_relation_mem (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (I : Ideal A) (hpI : (p : A) ∈ I) (d x a : A) (hdI : d ∈ I)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, D.delta^[i] (d * x - a) ∈ I) :
    D.delta^[n + 2] (d * x - a) ∈ I ↔ deltaDivisionWittRelationElement D d x a u n ∈ I := by
  have he := deltaDivision_next_jet_zero_iff_witt_relation_map_zero D hp hg
    (Ideal.Quotient.mk I) (Ideal.Quotient.eq_zero_iff_mem.mpr hpI) d x a
    (Ideal.Quotient.eq_zero_iff_mem.mpr hdI) u hu n
    (fun i hi => Ideal.Quotient.eq_zero_iff_mem.mpr (hlower i hi))
  simpa only [Ideal.Quotient.eq_zero_iff_mem] using he

/-- 下位イデアルに次段δ生成元を加える操作は、Witt根関係元を加える操作に一致する。 -/
theorem deltaDivision_next_jet_sup_span_eq_witt_relation (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (I : Ideal A) (hpI : (p : A) ∈ I) (d x a : A) (hdI : d ∈ I)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ i ≤ n + 1, D.delta^[i] (d * x - a) ∈ I) :
    I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))} =
      I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} := by
  apply le_antisymm
  · have hI : I ≤ I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} := le_sup_left
    have hS : Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} ≤
        I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)} := le_sup_right
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg
      (I ⊔ Ideal.span {(deltaDivisionWittRelationElement D d x a u n)})
      (hI hpI) d x a (hI hdI) u hu n
      (fun i hi => hI (hlower i hi))).mpr
    exact hS (Ideal.mem_span_singleton_self _)
  · have hI : I ≤ I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))} := le_sup_left
    have hS : Ideal.span {(D.delta^[n + 2] (d * x - a))} ≤
        I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))} := le_sup_right
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg
      (I ⊔ Ideal.span {(D.delta^[n + 2] (d * x - a))})
      (hI hpI) d x a (hI hdI) u hu n
      (fun i hi => hI (hlower i hi))).mp
    exact hS (Ideal.mem_span_singleton_self _)

/-- 任意族の次段δ生成元は、下位イデアル上で同時にWitt根関係元へ置き換えられる。 -/
theorem deltaDivision_family_next_jets_sup_span_eq_witt_relations {σ : Type v}
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (I : Ideal A) (hpI : (p : A) ∈ I) (d : A) (x a : σ → A) (hdI : d ∈ I)
    (u : Aˣ) (hu : (u : A) = D.delta d) (n : ℕ)
    (hlower : ∀ s i, i ≤ n + 1 → D.delta^[i] (d * x s - a s) ∈ I) :
    I ⊔ Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) =
      I ⊔ Ideal.span
        (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) := by
  apply le_antisymm
  · have hI : I ≤ I ⊔ Ideal.span
        (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) := le_sup_left
    have hS : Ideal.span
        (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) ≤
        I ⊔ Ideal.span
          (Set.range (fun s => deltaDivisionWittRelationElement D d (x s) (a s) u n)) :=
      le_sup_right
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg _ (hI hpI)
      d (x s) (a s) (hI hdI) u hu n (fun i hi => hI (hlower s i hi))).mpr
    exact hS (Ideal.subset_span (Set.mem_range.mpr ⟨s, rfl⟩))
  · have hI : I ≤ I ⊔ Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) :=
      le_sup_left
    have hS : Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) ≤
        I ⊔ Ideal.span (Set.range (fun s => D.delta^[n + 2] (d * x s - a s))) := le_sup_right
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    apply (deltaDivision_next_jet_mem_iff_witt_relation_mem D hp hg _ (hI hpI)
      d (x s) (a s) (hI hdI) u hu n (fun i hi => hI (hlower s i hi))).mp
    exact hS (Ideal.subset_span (Set.mem_range.mpr ⟨s, rfl⟩))

end SerrePositivity.BhattScholze

end DeltaDivisionWittRelationIdeal

/-! ## 実際の有限δ関係イデアルの全段Witt根生成元表示

既存の有限δイデアルと第一剰余イデアルを使い、後続式を反復する。
-/

@[expose] public noncomputable section DeltaDivisionWittFiniteRelationIdeal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 相対自由環の指定生成元に対応する、源の具体的Witt根関係元。 -/
def deltaDivisionRelativeWittRelationElement (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) : RelativeFreeDeltaRing (R := A) σ :=
  deltaDivisionWittRelationElement (relativeFreeDeltaStructure σ D) (MvPolynomial.C d)
    (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s))
    (u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)) n

/-- 深さ2からの初期N段のWitt根関係元族で生成した通常イデアル。 -/
def deltaDivisionFiniteWittRelationIdeal (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin N =>
    deltaDivisionRelativeWittRelationElement D d a u z.1 z.2.val)

/-- 零段のWitt根関係イデアルは零。 -/
@[simp] theorem deltaDivisionFiniteWittRelationIdeal_zero (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) : deltaDivisionFiniteWittRelationIdeal D d a u 0 = ⊥ := by
  apply le_bot_iff.mp
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, i⟩, rfl⟩
  exact Fin.elim0 i

/-- 初期Witt根関係イデアルは次の族を添加して得られる。 -/
theorem deltaDivisionFiniteWittRelationIdeal_succ (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    deltaDivisionFiniteWittRelationIdeal D d a u (N + 1) =
      deltaDivisionFiniteWittRelationIdeal D d a u N ⊔
        Ideal.span (Set.range fun s => deltaDivisionRelativeWittRelationElement D d a u s N) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    change deltaDivisionRelativeWittRelationElement D d a u s i.val ∈ _
    by_cases hi : i.val < N
    · apply (show deltaDivisionFiniteWittRelationIdeal D d a u N ≤ _ from le_sup_left)
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨i.val, hi⟩), rfl⟩)
    · have he : i.val = N := by omega
      rw [he]
      apply (show Ideal.span
          (Set.range fun s => deltaDivisionRelativeWittRelationElement D d a u s N) ≤
        deltaDivisionFiniteWittRelationIdeal D d a u N ⊔ _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, i⟩, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, i.castSucc), rfl⟩)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, Fin.last N), rfl⟩)

/-- 実際の有限δ関係イデアルの次段は、下位イデアルにWitt根関係元族を加えたもの。 -/
theorem deltaDivisionFiniteRelationIdeal_succ_witt (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (hp : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (n : ℕ) :
    Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      deltaDivisionFiniteRelationIdeal D d a (n + 2) =
    (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      deltaDivisionFiniteRelationIdeal D d a (n + 1)) ⊔
        Ideal.span (Set.range fun s => deltaDivisionRelativeWittRelationElement D d a u s n) := by
  let E := relativeFreeDeltaStructure σ D
  let I := Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    deltaDivisionFiniteRelationIdeal D d a (n + 1)
  have hc : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤ I := le_sup_left
  have hr : deltaDivisionFiniteRelationIdeal D d a (n + 1) ≤ I := le_sup_right
  have hpI : (p : RelativeFreeDeltaRing (R := A) σ) ∈ I := hc (Ideal.subset_span (by simp))
  have hdI : MvPolynomial.C d ∈ I := hc (Ideal.subset_span (by simp))
  have hlow (s : σ) (i : ℕ) (hi : i ≤ n + 1) :
      E.delta^[i] (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) ∈ I := by
    apply hr
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨i, by omega⟩), rfl⟩)
  have hu' : ((u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ) :
      (RelativeFreeDeltaRing (R := A) σ)ˣ) : RelativeFreeDeltaRing (R := A) σ) =
        E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (u : A) = _
    rw [hu, relativeFreeDeltaStructure_delta_C]
  have he := deltaDivision_family_next_jets_sup_span_eq_witt_relations E hp hg I hpI
    (MvPolynomial.C d) (fun s => MvPolynomial.X (s, 0)) (fun s => MvPolynomial.C (a s))
    hdI (u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)) hu' n hlow
  rw [deltaDivisionFiniteRelationIdeal_succ D d a (n + 1), ← sup_assoc]
  exact he

/-- 全有限δ剰余イデアルは第一剰余イデアルと初期Witt根関係元族で生成される。 -/
theorem deltaDivisionFiniteRelationIdeal_eq_first_sup_witt (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (hp : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (N : ℕ) :
    Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      deltaDivisionFiniteRelationIdeal D d a (N + 1) =
        deltaDivisionFirstResidueIdeal D d a ⊔ deltaDivisionFiniteWittRelationIdeal D d a u N := by
  induction N with
  | zero => rw [deltaDivisionFiniteWittRelationIdeal_zero, sup_bot_eq]; rfl
  | succ N ih =>
      change Ideal.span _ ⊔ deltaDivisionFiniteRelationIdeal D d a (N + 2) = _
      rw [deltaDivisionFiniteRelationIdeal_succ_witt D d a u hu hp hg N, ih,
        deltaDivisionFiniteWittRelationIdeal_succ, sup_assoc]

end SerrePositivity.BhattScholze

end DeltaDivisionWittFiniteRelationIdeal

/-! ## 逆Witt座標での具体的モニック有限関係式

最高変数のp乗と初期段の係数多項式を分離する。
-/

@[expose] public noncomputable section DeltaDivisionWittNormalizedRelation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 正規化した第n関係式の下位有限変数だけの係数。 -/
def deltaDivisionWittNormalizedCoefficient (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) : MvPolynomial (σ × Fin (n + 1)) A :=
  MvPolynomial.C ((u⁻¹ : Aˣ) : A) ^ (p ^ (n + 1)) *
    (MvPolynomial.C ((deltaWittGhostVector D (a s)).coeff (n + 2)) -
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin (n + 1) => MvPolynomial.X (s, i))
        (wittDivisionRemainderPolynomial (deltaWittGhostVector D d) n))

/-- 下位係数多項式の標準包含像。 -/
theorem deltaDivisionWittNormalizedCoefficient_image (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
      (deltaDivisionWittNormalizedCoefficient D d a u s n) =
    MvPolynomial.C ((u⁻¹ : Aˣ) : A) ^ (p ^ (n + 1)) *
      (MvPolynomial.C ((deltaWittGhostVector D (a s)).coeff (n + 2)) -
        MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i : Fin (n + 1) => MvPolynomial.X (s, i.val))
          (wittDivisionRemainderPolynomial (deltaWittGhostVector D d) n)) := by
  let f := (relativeFreeFiniteInitialPolynomialMap (n + 1) σ A).toRingHom
  have hC (b : A) : f (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [f, relativeFreeFiniteInitialPolynomialMap]
  have hX (i : Fin (n + 1)) : f (MvPolynomial.X (s, i)) = MvPolynomial.X (s, i.val) := by
    simp [f, relativeFreeFiniteInitialPolynomialMap]
  have he := MvPolynomial.map_eval₂Hom MvPolynomial.C
    (fun i : Fin (n + 1) => MvPolynomial.X (s, i)) f
    (wittDivisionRemainderPolynomial (deltaWittGhostVector D d) n)
  have hfc : f.comp MvPolynomial.C = MvPolynomial.C := by
    apply RingHom.ext
    exact hC
  have hfx : (fun i : Fin (n + 1) => f (MvPolynomial.X (s, i))) =
      fun i => MvPolynomial.X (s, i.val) := funext hX
  rw [hfc, hfx] at he
  change f (deltaDivisionWittNormalizedCoefficient D d a u s n) = _
  rw [deltaDivisionWittNormalizedCoefficient, map_mul, map_pow, map_sub, hC, hC, he]

/-- 最高有限変数のp乗から初期段係数を引いた、具体的なモニック有限関係式。 -/
def deltaDivisionWittNormalizedPolynomial (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) : MvPolynomial (σ × Fin (n + 2)) A :=
  MvPolynomial.X (s, Fin.last (n + 1)) ^ p -
    relativeFreeFiniteStepInclusion n σ (deltaDivisionWittNormalizedCoefficient D d a u s n)

/-- 正規化した有限関係式の包含像は最高変数のp乗から下位係数を引いた式。 -/
theorem deltaDivisionWittNormalizedPolynomial_image (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
      (deltaDivisionWittNormalizedPolynomial D d a u s n) =
      MvPolynomial.X (s, n + 1) ^ p -
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
          (deltaDivisionWittNormalizedCoefficient D d a u s n) := by
  rw [deltaDivisionWittNormalizedPolynomial, map_sub, map_pow]
  have hx : relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
      (MvPolynomial.X (s, Fin.last (n + 1))) = MvPolynomial.X (s, n + 1) := by
    simp [relativeFreeFiniteInitialPolynomialMap]
  rw [hx]
  congr 1
  exact RingHom.congr_fun (relativeFreeFiniteStepInclusion_comp_initial (A := A) n σ) _

/-- 実際の源Witt根関係元の逆座標像は、構成した有限モニック関係式の包含像。 -/
theorem deltaDivisionRelativeWittRelationElement_inverse_image (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeWittInverseMap D hp (deltaDivisionRelativeWittRelationElement D d a u s n) =
      relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a u s n) := by
  let E := relativeFreeDeltaStructure σ D
  let q := (relativeFreeWittInverseMap (σ := σ) D hp).toRingHom
  have hX (i : ℕ) : q ((deltaWittGhostVector E (MvPolynomial.X (s, 0))).coeff i) =
      MvPolynomial.X (s, i) := by
    change relativeFreeWittInverseMap D hp (relativeFreeWittGhostCoefficient D s i) = _
    exact relativeFreeWittInverseMap_coefficient D hp s i
  have hC (b : A) (i : ℕ) : q ((deltaWittGhostVector E (MvPolynomial.C b)).coeff i) =
      MvPolynomial.C ((deltaWittGhostVector D b).coeff i) := by
    exact relativeFreeWittInverseMap_coefficient_C D hp hg b i
  have hqC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b :=
    AlgHom.commutes (relativeFreeWittInverseMap D hp) b
  have hw : WittVector.map q (deltaWittGhostVector E (MvPolynomial.C d)) =
      WittVector.map MvPolynomial.C (deltaWittGhostVector D d) :=
    (relativeFreeWittInverseMap_wittVector_C D hp hg d).trans
      (deltaWittGhostVector_relativeFree_C D hg d)
  have huq :
      ((((u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ))).map
        q.toMonoidHom)⁻¹ :
      (RelativeFreeDeltaRing (R := A) σ)ˣ) =
      (u⁻¹).map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ) := by
    apply Units.ext
    change q (MvPolynomial.C ((u⁻¹ : Aˣ) : A)) = MvPolynomial.C ((u⁻¹ : Aˣ) : A)
    exact hqC _
  have huqv := congrArg Units.val huq
  unfold deltaDivisionRelativeWittRelationElement
  change q (deltaDivisionWittRelationElement E (MvPolynomial.C d) (MvPolynomial.X (s, 0))
    (MvPolynomial.C (a s))
    (u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)) n) = _
  rw [deltaDivisionWittRelationElement_map]
  simp only [deltaDivisionWittRootPolynomial, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  simp only [hX, hC]
  rw [hw, ← wittDivisionRemainderPolynomial_map, MvPolynomial.eval₂Hom_map_hom]
  rw [deltaDivisionWittNormalizedPolynomial_image, deltaDivisionWittNormalizedCoefficient_image]
  congr 1
  apply congrArg₂ (fun b c : RelativeFreeDeltaRing (R := A) σ => b * c)
  · apply congrArg (fun b : RelativeFreeDeltaRing (R := A) σ => b ^ (p ^ (n + 1)))
    exact huqv
  · rfl

/-- 最高変数分離後の関係式は、各変数のp乗から下位係数を引いたモニック冪形。 -/
theorem deltaDivisionWittNormalizedPolynomial_top_split (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeFiniteTopVariableSplitAlgEquiv n σ A
      (deltaDivisionWittNormalizedPolynomial D d a u s n) =
        MvPolynomial.X s ^ p -
          MvPolynomial.C (deltaDivisionWittNormalizedCoefficient D d a u s n) := by
  rw [deltaDivisionWittNormalizedPolynomial, map_sub, map_pow,
    relativeFreeFiniteTopVariableSplitAlgEquiv_X_top,
    relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion]

end SerrePositivity.BhattScholze

end DeltaDivisionWittNormalizedRelation

/-! ## 逆Witt座標による全有限関係イデアルの正規化

実際の有限δイデアルの全段式を、具体的モニック関係元族へ移す。
-/

@[expose] public noncomputable section DeltaDivisionWittNormalizedIdeal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期N段の正規化有限モニック関係式の包含像で生成したイデアル。 -/
def deltaDivisionFiniteNormalizedWittIdeal (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin N =>
    relativeFreeFiniteInitialPolynomialMap (z.2.val + 2) σ A
      (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val))

/-- 逆座標射による実際のWitt根関係イデアルの像は正規化モニックイデアル。 -/
theorem deltaDivisionFiniteWittRelationIdeal_inverse_map (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.map (relativeFreeWittInverseMap D hp).toRingHom
      (deltaDivisionFiniteWittRelationIdeal D d a u N) =
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  rw [deltaDivisionFiniteWittRelationIdeal, Ideal.map_span,
    deltaDivisionFiniteNormalizedWittIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (deltaDivisionRelativeWittRelationElement_inverse_image
      D hp hg d a u z.1 z.2.val).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, deltaDivisionRelativeWittRelationElement_inverse_image
      D hp hg d a u z.1 z.2.val⟩

/-- 逆Witt座標射は、既存第一剰余イデアルを固定する。 -/
theorem deltaDivisionFirstResidueIdeal_inverse_map (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    Ideal.map (relativeFreeWittInverseMap D hp).toRingHom
      (deltaDivisionFirstResidueIdeal D d a) = deltaDivisionFirstResidueIdeal D d a := by
  let q := (relativeFreeWittInverseMap (σ := σ) D hp).toRingHom
  have hC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b :=
    AlgHom.commutes (relativeFreeWittInverseMap D hp) b
  have hX (s : σ) : q (MvPolynomial.X (s, 0)) = MvPolynomial.X (s, 0) := by
    change relativeFreeWittInverseMap D hp (MvPolynomial.X (s, 0)) = _
    have h := relativeFreeWittInverseMap_coefficient D hp s 0
    simpa only [relativeFreeWittGhostCoefficient_zero] using h
  have hA : q '' (Set.range fun s => MvPolynomial.C (a s)) =
      Set.range fun s => MvPolynomial.C (a s) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hC _).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hC _⟩
  have hroot (s : σ) : q (MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      MvPolynomial.X (s, 0) ^ p - MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    rw [map_sub, map_pow, hX, hC]
  have hR : q '' (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      Set.range fun s => MvPolynomial.X (s, 0) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hroot s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hroot s⟩
  rw [deltaDivisionFirstResidueIdeal_eq_monic D d a u hu]
  change Ideal.map q (deltaDivisionFirstMonicIdeal D d a u) = _
  simp only [deltaDivisionFirstMonicIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, map_natCast, hC, hA, hR]

/-- 全有限δ剰余イデアルの逆座標像は、第一段の像と正規化モニックイデアルの和。 -/
theorem deltaDivisionFiniteRelationIdeal_inverse_map (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1)) =
      Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
        (deltaDivisionFirstResidueIdeal D d a) ⊔
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  rw [deltaDivisionFiniteRelationIdeal_eq_first_sup_witt D d a u hu hpL hg,
    Ideal.map_sup, deltaDivisionFiniteWittRelationIdeal_inverse_map D hpA hg]

/-- 全有限δ剰余イデアルの逆座標像は、第一剰余と具体的モニック関係元族の和。 -/
theorem deltaDivisionFiniteRelationIdeal_inverse_map_eq_first_sup_normalized
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1)) =
      deltaDivisionFirstResidueIdeal D d a ⊔
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  rw [deltaDivisionFiniteRelationIdeal_inverse_map D hpA hpL hg d a u hu,
    deltaDivisionFirstResidueIdeal_inverse_map D hpA d a u hu]

end SerrePositivity.BhattScholze

end DeltaDivisionWittNormalizedIdeal

/-! ## 実際の有限δ剰余商と正規化モニック商の同型 -/

@[expose] public noncomputable section DeltaDivisionWittNormalizedQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 実際の有限δ剰余商を、具体的モニック関係式の商へ移す環同型。 -/
def deltaDivisionFiniteNormalizedQuotientEquiv (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1))) ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (deltaDivisionFirstResidueIdeal D d a ⊔
          deltaDivisionFiniteNormalizedWittIdeal D d a u N)) :=
  Ideal.quotientEquiv _ _ (relativeFreeWittCoordinateEquiv D hpA).symm.toRingEquiv
    (deltaDivisionFiniteRelationIdeal_inverse_map_eq_first_sup_normalized
      D hpA hpL hg d a u hu N).symm

/-- 正規化商同型と、実際の源環の標準商射の図式。 -/
theorem deltaDivisionFiniteNormalizedQuotientEquiv_mk (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a u hu N
      (Ideal.Quotient.mk _ f) =
        Ideal.Quotient.mk _ (relativeFreeWittInverseMap D hpA f) := by
  rfl

/-- 正規化商同型は基底係数の標準像を固定する。 -/
theorem deltaDivisionFiniteNormalizedQuotientEquiv_C (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) (b : A) :
    deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a u hu N
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
        Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  rw [deltaDivisionFiniteNormalizedQuotientEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _) (AlgHom.commutes (relativeFreeWittInverseMap D hpA) b)

end SerrePositivity.BhattScholze

end DeltaDivisionWittNormalizedQuotient

/-! ## 正規化関係イデアルの初期有限変数による表示 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedPresentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期N段の各モニック関係式を初期N+1変数の環に置いた生成元。 -/
def deltaDivisionFiniteNormalizedGenerator (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (z : σ × Fin N) :
    MvPolynomial (σ × Fin (N + 1)) A :=
  MvPolynomial.rename
    (fun w : σ × Fin (z.2.val + 2) => (w.1, (⟨w.2.val, by omega⟩ : Fin (N + 1))))
    (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val)

/-- 有限環に置いた生成元の包含像は元のモニック関係式の包含像。 -/
theorem deltaDivisionFiniteNormalizedGenerator_image (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (z : σ × Fin N) :
    relativeFreeFiniteInitialPolynomialMap (N + 1) σ A
      (deltaDivisionFiniteNormalizedGenerator D d a u N z) =
      relativeFreeFiniteInitialPolynomialMap (z.2.val + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val) := by
  unfold deltaDivisionFiniteNormalizedGenerator relativeFreeFiniteInitialPolynomialMap
  rw [MvPolynomial.rename_rename]
  rfl

/-- 第一段の係数・モニック関係と全初期N段の関係を有限環に置いたイデアル。 -/
def deltaDivisionFiniteNormalizedPresentationIdeal (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : Ideal (MvPolynomial (σ × Fin (N + 1)) A) :=
  ((Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))) ⊔
    Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N))

/-- 有限表示イデアルの包含像は実際の正規化イデアルに一致する。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_map_initial (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    Ideal.map (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) =
      deltaDivisionFirstResidueIdeal D d a ⊔
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  let q := (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
  have hC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [q, relativeFreeFiniteInitialPolynomialMap]
  have hX (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1)))) =
      MvPolynomial.X (s, 0) := by
    simp [q, relativeFreeFiniteInitialPolynomialMap]
  have hA : q '' (Set.range fun s => MvPolynomial.C (a s)) =
      Set.range fun s => MvPolynomial.C (a s) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hC _).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hC _⟩
  have hroot (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      MvPolynomial.X (s, 0) ^ p - MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    rw [map_sub, map_pow, hX, hC]
  have hR : q '' (Set.range fun s =>
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      Set.range fun s => MvPolynomial.X (s, 0) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hroot s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hroot s⟩
  have hG : q '' Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N) =
      Set.range (fun z : σ × Fin N => relativeFreeFiniteInitialPolynomialMap (z.2.val + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (deltaDivisionFiniteNormalizedGenerator_image D d a u N z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, deltaDivisionFiniteNormalizedGenerator_image D d a u N z⟩
  rw [deltaDivisionFirstResidueIdeal_eq_monic D d a u hu]
  change Ideal.map q _ = _
  simp only [deltaDivisionFiniteNormalizedPresentationIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, map_natCast, hC, hA, hR, hG,
    deltaDivisionFirstMonicIdeal, deltaDivisionFiniteNormalizedWittIdeal]

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedPresentation

/-! ## 有限正規化関係イデアルの後続式 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedStep

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 既存の有限正規化生成元は、次段への標準包含に整合する。 -/
theorem deltaDivisionFiniteNormalizedGenerator_castSucc (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (z : σ × Fin N) :
    relativeFreeFiniteStepInclusion N σ (deltaDivisionFiniteNormalizedGenerator D d a u N z) =
      deltaDivisionFiniteNormalizedGenerator D d a u (N + 1) (z.1, z.2.castSucc) := by
  unfold relativeFreeFiniteStepInclusion deltaDivisionFiniteNormalizedGenerator
  change MvPolynomial.rename _ (MvPolynomial.rename _ _) = MvPolynomial.rename _ _
  rw [MvPolynomial.rename_rename]
  rfl

/-- 次段の最上段生成元は、第Nモニック有限関係式そのもの。 -/
theorem deltaDivisionFiniteNormalizedGenerator_last (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (s : σ) :
    deltaDivisionFiniteNormalizedGenerator D d a u (N + 1) (s, Fin.last N) =
      deltaDivisionWittNormalizedPolynomial D d a u s N := by
  unfold deltaDivisionFiniteNormalizedGenerator
  change MvPolynomial.rename (fun w : σ × Fin (N + 2) => (w.1, w.2)) _ = _
  exact MvPolynomial.rename_id_apply _

/-- 有限正規化生成元族のspanの次段は、前段の像と最上段関係式族の和。 -/
theorem deltaDivisionFiniteNormalizedGenerators_span_succ (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u (N + 1))) =
      Ideal.map (relativeFreeFiniteStepInclusion N σ)
        (Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N))) ⊔
      Ideal.span (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    by_cases hi : i.val < N
    · let j : Fin N := ⟨i.val, hi⟩
      have he : j.castSucc = i := Fin.ext rfl
      rw [← he, ← deltaDivisionFiniteNormalizedGenerator_castSucc D d a u N (s, j)]
      apply (show Ideal.map (relativeFreeFiniteStepInclusion N σ)
          (Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N))) ≤
        _ from le_sup_left)
      apply Ideal.mem_map_of_mem
      exact Ideal.subset_span (Set.mem_range_self (s, j))
    · have he : i = Fin.last N := Fin.ext (by simp; omega)
      rw [he, deltaDivisionFiniteNormalizedGenerator_last]
      apply (show Ideal.span
          (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) ≤
        _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
  · apply sup_le
    · rw [Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      rw [deltaDivisionFiniteNormalizedGenerator_castSucc]
      exact Ideal.subset_span (Set.mem_range_self (z.1, z.2.castSucc))
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      change deltaDivisionWittNormalizedPolynomial D d a u s N ∈ _
      rw [← deltaDivisionFiniteNormalizedGenerator_last D d a u N s]
      exact Ideal.subset_span (Set.mem_range_self (s, Fin.last N))

/-- 有限正規化イデアルの次段は、前段の包含像にモニック関係式族を加えたもの。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_succ (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    deltaDivisionFiniteNormalizedPresentationIdeal D d a u (N + 1) =
      Ideal.map (relativeFreeFiniteStepInclusion N σ)
        (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ⊔
      Ideal.span (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) := by
  let q := relativeFreeFiniteStepInclusion (A := A) N σ
  have hC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [q, relativeFreeFiniteStepInclusion]
  have hX (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1)))) =
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 2))) := by
    simp [q, relativeFreeFiniteStepInclusion]
  have hA : q '' (Set.range fun s => MvPolynomial.C (a s)) =
      Set.range fun s => MvPolynomial.C (a s) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hC _).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hC _⟩
  have hroot (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 2))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    rw [map_sub, map_pow, hX, hC]
  have hR : q '' (Set.range fun s =>
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      Set.range fun s => MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 2))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hroot s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hroot s⟩
  change deltaDivisionFiniteNormalizedPresentationIdeal D d a u (N + 1) =
    Ideal.map q (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ⊔ _
  have hG := deltaDivisionFiniteNormalizedGenerators_span_succ D d a u N
  unfold deltaDivisionFiniteNormalizedPresentationIdeal
  rw [hG]
  simp only [Ideal.map_sup]
  simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_natCast, hC, hA, hR]
  exact (sup_assoc _ _ _).symm

/-- 最高変数分離後の次段イデアルは、前段係数イデアルとモニック冪族の和。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_map_top_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.map (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a u (N + 1)) =
      Ideal.map MvPolynomial.C (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ⊔
      Ideal.span (Set.range fun s => MvPolynomial.X s ^ p -
        MvPolynomial.C (deltaDivisionWittNormalizedCoefficient D d a u s N)) := by
  let f := (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom
  have hc : f.comp (relativeFreeFiniteStepInclusion N σ) = MvPolynomial.C := by
    apply RingHom.ext
    intro b
    exact relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion N σ A b
  have hs : f '' (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) =
      Set.range (fun s => MvPolynomial.X s ^ p -
        MvPolynomial.C (deltaDivisionWittNormalizedCoefficient D d a u s N)) := by
    ext b
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (deltaDivisionWittNormalizedPolynomial_top_split D d a u s N).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, deltaDivisionWittNormalizedPolynomial_top_split D d a u s N⟩
  change Ideal.map f _ = _
  rw [deltaDivisionFiniteNormalizedPresentationIdeal_succ, Ideal.map_sup,
    Ideal.map_map, hc, Ideal.map_span, hs]

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedStep

/-! ## 下位関係商におけるδ反復関係とWitt根関係の正則性

既存の主イデアル置換等式を使用する。p正則性・ghost単射・δd単元条件を明示する。
-/

@[expose] public noncomputable section DeltaDivisionWittJetRegularity

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hp : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (I : Ideal A) (hpI : (p : A) ∈ I) (d x a : A) (hdI : d ∈ I)
variable (v : Aˣ) (hv : (v : A) = D.delta d) (n : ℕ)
variable (hlower : ∀ i ≤ n + 1, D.delta^[i] (d * x - a) ∈ I)
include hp hg hpI hdI hv hlower

/-- 下位関係商内では、次段δ反復関係とWitt根関係が同じ主イデアルを生成する。 -/
theorem deltaDivision_next_jet_quotient_span_eq_witt :
    Ideal.span {Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))} =
      Ideal.span {Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n)} := by
  have h := congrArg (Ideal.map (Ideal.Quotient.mk I))
    (deltaDivision_next_jet_sup_span_eq_witt_relation D hp hg I hpI d x a hdI v hv n hlower)
  simpa only [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    Ideal.map_span, Set.image_singleton] using h

/-- 商内の元のδ反復関係が非零因子であることは、Witt根関係の正則性と同値。 -/
theorem deltaDivision_next_jet_quotient_isSMulRegular_iff_witt :
    IsSMulRegular (A ⧸ I) (Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))) ↔
      IsSMulRegular (A ⧸ I)
        (Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n)) := by
  have go (r t : A ⧸ I) (he : Ideal.span {r} = Ideal.span {t})
      (ht : IsSMulRegular (A ⧸ I) t) : IsSMulRegular (A ⧸ I) r := by
    have hm : t ∈ Ideal.span {r} := he.symm ▸ Ideal.mem_span_singleton_self t
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
    have ht' : IsRegular t := isLeftRegular_iff_isRegular.mp ht
    rw [hc] at ht'
    exact ht'.of_mul_left.left
  have he := deltaDivision_next_jet_quotient_span_eq_witt D hp hg I hpI d x a hdI v hv n hlower
  exact ⟨go _ _ he.symm, go _ _ he⟩

/-- 商内のWitt根関係が正則なら、元の次段δ反復関係の実Koszul分解を得る。 -/
theorem deltaDivision_next_jet_quotient_isKoszulResolution
    (hreg : IsSMulRegular (A ⧸ I)
      (Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n))) :
    SerrePositivity.IsKoszulResolution
      (fun _ : Fin 1 ↦ Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact (deltaDivision_next_jet_quotient_isSMulRegular_iff_witt
    D hp hg I hpI d x a hdI v hv n hlower).mpr hreg

/-- 元のδ反復関係による導来商は、共通の実Koszul錐関手と自然同型。 -/
def deltaDivision_next_jet_quotient_derivedKoszulNatIso
    (hreg : IsSMulRegular (A ⧸ I)
      (Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n))) :
    boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))})) ⋙
      boundedAboveDerivedRestrictScalars
        (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))})) ⋙
      DerivedCategory.Minus.ι ≅
    DerivedCategory.Minus.ι ⋙ DerivedCompletion.derivedScalarConeFunctor (A ⧸ I)
      (Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))) :=
  restrictedDerivedQuotientKoszulNatIso _
    ((deltaDivision_next_jet_quotient_isSMulRegular_iff_witt
      D hp hg I hpI d x a hdI v hv n hlower).mpr hreg)

end SerrePositivity.BhattScholze

end DeltaDivisionWittJetRegularity
