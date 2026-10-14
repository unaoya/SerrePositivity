module

public import SerrePositivity.BhattScholze.DeltaDivisionWittMonicRelations
public import SerrePositivity.BhattScholze.WittDivisionPolynomialRemainder

/-! # 実際のδ除算関係式の次段と具体的モニック多項式の根条件

下位関係式を仮定して、次の関係式の消滅を双方向に比較する。
-/

@[expose] public noncomputable section
universe u v
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
