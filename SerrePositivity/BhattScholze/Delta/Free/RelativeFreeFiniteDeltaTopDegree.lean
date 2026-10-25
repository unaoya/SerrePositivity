module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteTopVariableSplit
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDeltaLinearization
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! # 有限δ像の最高変数に関するp剰余次数評価

最高変数を分離し、係数側だけをpで割る具体的な環射を使う。
係数商にδ構造を仮定しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限変数の多項式環のp商。零環も許す。 -/
abbrev RelativeFreeFiniteOldResidue :=
  MvPolynomial (σ × Fin (N + 1)) A ⧸ Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)}

/-- 最高変数を外側へ分離して係数をpで割る標準射。 -/
def relativeFreeFiniteTopResidueMap :
    MvPolynomial (σ × Fin (N + 2)) A →+*
      MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ) :=
  (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)}))).comp
    (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom

/-- 初期多項式の包含像はp商の係数。 -/
@[simp] theorem relativeFreeFiniteTopResidueMap_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C (Ideal.Quotient.mk _ f) := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A _) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion, MvPolynomial.map_C]

/-- 標準射はpを消す。 -/
theorem relativeFreeFiniteTopResidueMap_prime :
    relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
      (p : MvPolynomial (σ × Fin (N + 2)) A) = 0 := by
  rw [show (p : MvPolynomial (σ × Fin (N + 2)) A) =
    relativeFreeFiniteStepInclusion N σ (p : MvPolynomial (σ × Fin (N + 1)) A) from
      (map_natCast (relativeFreeFiniteStepInclusion N σ) p).symm,
    relativeFreeFiniteTopResidueMap_inclusion]
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self (p : MvPolynomial (σ × Fin (N + 1)) A))
  rw [h, MvPolynomial.C_0]

/-- 最高変数の像は外側の変数。 -/
@[simp] theorem relativeFreeFiniteTopResidueMap_X_top (s : σ) :
    relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ (MvPolynomial.X (s, Fin.last (N + 1))) =
      MvPolynomial.X s := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A _) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, MvPolynomial.map_X]

/-- 初期変数の像は係数側の変数。 -/
@[simp] theorem relativeFreeFiniteTopResidueMap_X_initial (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ (MvPolynomial.X (s, i.castSucc)) =
      MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X (s, i))) := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A _) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_initial, MvPolynomial.map_C]

/-- 初期多項式の包含像の任意冪は、最高変数に関して次数0。 -/
theorem relativeFreeFiniteTopResidueMap_inclusion_pow_degree
    (f : MvPolynomial (σ × Fin (N + 1)) A) (m : ℕ) :
    ((relativeFreeFiniteTopResidueMap (p := p) N σ
      (relativeFreeFiniteStepInclusion N σ f)) ^ m).totalDegree = 0 := by
  rw [relativeFreeFiniteTopResidueMap_inclusion, ← map_pow, MvPolynomial.totalDegree_C]

/-- 次変数の像は最高変数について次数1以下。係数商が零環でも成立する。 -/
theorem relativeFreeFiniteTopResidueMap_X_succ_degree (s : σ) (i : Fin (N + 1)) :
    (relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
      (MvPolynomial.X (s, i.succ))).totalDegree ≤ 1 := by
  by_cases hi : i.val < N
  · let j : Fin (N + 1) := ⟨i.val + 1, by omega⟩
    have he : i.succ = j.castSucc := Fin.ext rfl
    rw [he, relativeFreeFiniteTopResidueMap_X_initial, MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1
  · have he : i.succ = Fin.last (N + 1) := by
      apply Fin.ext
      have hn := i.isLt
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [he, relativeFreeFiniteTopResidueMap_X_top]
    rcases subsingleton_or_nontrivial
      (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ) with h | h
    · let := h
      have hz : (MvPolynomial.X s :
          MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ)) = 0 :=
        Subsingleton.elim _ _
      rw [hz, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le 1
    · let := h
      rw [MvPolynomial.totalDegree_X]

variable [Fact p.Prime]

/-- rank 1補助δ計算の像は初期係数だけを使う。 -/
theorem relativeFreeFiniteTopResidueMap_rankOneStep (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteRankOneStep N σ D f) =
      MvPolynomial.C (Ideal.Quotient.mk _
        ((polynomialRankOneDeltaStructure (σ × Fin (N + 1)) D).delta f)) :=
  relativeFreeFiniteTopResidueMap_inclusion N σ _

/-- p剰余で有限δ差の最高変数全体の次数は1以下。 -/
theorem relativeFreeFiniteDeltaDifference_top_degree (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteDeltaDifference N σ D
      (relativeFreeFiniteTopResidueMap (p := p) N σ) f).totalDegree ≤ 1 := by
  classical
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  rw [relativeFreeFiniteDeltaDifference_polynomial_old_coefficients N σ D q
    (relativeFreeFiniteTopResidueMap_prime N σ)]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  have hinner : (s.sum (fun z k => (q (relativeFreeFiniteStepInclusion N σ
      (MvPolynomial.monomial (s - Finsupp.single z 1) (k : A)))) ^ p *
        q (MvPolynomial.X (z.1, z.2.succ)))).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro z hz
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [relativeFreeFiniteTopResidueMap_inclusion_pow_degree, zero_add]
    exact relativeFreeFiniteTopResidueMap_X_succ_degree N σ z.1 z.2
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [relativeFreeFiniteTopResidueMap_inclusion_pow_degree, zero_add]
  exact hinner

/-- 任意有限δ像のp剰余は、最高変数全体に関して次数1以下。 -/
theorem relativeFreeFiniteDeltaStep_top_degree (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteTopResidueMap (p := p) N σ
      (relativeFreeFiniteDeltaStep N σ D f)).totalDegree ≤ 1 := by
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  have he : q (relativeFreeFiniteDeltaStep N σ D f) =
      relativeFreeFiniteDeltaDifference N σ D q f + q (relativeFreeFiniteRankOneStep N σ D f) := by
    exact (sub_add_cancel _ _).symm
  rw [he, relativeFreeFiniteTopResidueMap_rankOneStep]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact relativeFreeFiniteDeltaDifference_top_degree N σ D f
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1

end SerrePositivity.BhattScholze
