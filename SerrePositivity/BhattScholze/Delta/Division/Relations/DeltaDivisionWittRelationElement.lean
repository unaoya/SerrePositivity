module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionWittPolynomialRelations

/-! # 源のWitt根関係元と通常射での自然性

源の指定単元を使い、根多項式の評価を実際の環元として固定する。
-/

@[expose] public noncomputable section
universe u v
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
