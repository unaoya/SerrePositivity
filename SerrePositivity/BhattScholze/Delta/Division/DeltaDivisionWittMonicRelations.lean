module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionWittJetRelations
public import SerrePositivity.BhattScholze.Delta.Division.WittDivisionTriangular

/-! # 実際のδ除算関係式からの全段Wittモニック方程式

有限δjet消滅を積係数等式へ移し、既存全段Witt三角形公式を使う。
-/

@[expose] public noncomputable section
universe u v
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
