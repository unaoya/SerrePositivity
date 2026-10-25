module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionIteratedRelations
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-! # 最初の実p除算関係と通常商のp正則性

任意の指定変数sについて、δ閉包前の一つの実関係式を扱う。
全δ関係商・完備化・分冪包の平坦性は結論しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
open scoped Pointwise
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A) (s : σ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) (fun t ↦ D.frobeniusLift (y t)) s 0
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : L₀)})

/-- 最初の実p除算関係のmod p像は指定元の係数像のp乗の負。 -/
theorem deltaPDivisionFirstRelation_mod_p :
    q₀ g₀ = -(q₀ (MvPolynomial.C (y s))) ^ p := by
  have hp : q₀ (MvPolynomial.C (p : A)) = 0 := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  change q₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
    MvPolynomial.C (D.frobeniusLift (y s))) = _
  rw [map_sub, map_mul, hp, zero_mul, zero_sub, D.frobeniusLift_apply,
    map_add, map_pow, map_mul, map_add, map_pow, map_mul, hp, zero_mul, add_zero]

variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) (y s)))

include hpA hy

/-- y_sが係数環のmod pで正則なら、実最初のp除算関係もL/pで正則。 -/
theorem deltaPDivisionFirstRelation_mod_p_isSMulRegular :
    IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)}) (q₀ g₀) := by
  let qA := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hφ : IsSMulRegular (A ⧸ Ideal.span {(p : A)} ) (qA (D.frobeniusLift (y s))) := by
    have hp : qA (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _)
    have he : qA (D.frobeniusLift (y s)) = qA (y s) ^ p := by
      rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
    rw [he]
    exact hy.pow p
  have hc := SerrePositivity.isSMulRegular_mod_of_flat (S := L₀)
    (p : A) (D.frobeniusLift (y s)) hpA hφ
  have hc' : IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)})
      (q₀ (MvPolynomial.C (D.frobeniusLift (y s)))) := by
    have aux (c : L₀) (he : c = (p : L₀))
        (h : IsSMulRegular (L₀ ⧸ Ideal.span {c})
          (Ideal.Quotient.mk (Ideal.span {c}) (MvPolynomial.C (D.frobeniusLift (y s))))) :
        IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)})
          (q₀ (MvPolynomial.C (D.frobeniusLift (y s)))) := by
      subst c
      exact h
    exact aux _ (map_natCast (algebraMap A L₀) p) hc
  have he : q₀ g₀ = -q₀ (MvPolynomial.C (D.frobeniusLift (y s))) := by
    change q₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
      MvPolynomial.C (D.frobeniusLift (y s))) = _
    rw [map_sub, map_mul, map_natCast (MvPolynomial.C : A →+* L₀) p,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : L₀)),
      zero_mul, zero_sub]
  rw [he]
  intro x z hxz
  apply hc'
  simpa only [neg_smul, neg_inj] using hxz

/-- δ閉包前の実最初の関係商には新しいpねじれが生じない。 -/
theorem deltaPDivisionFirstRelation_quotient_p_mul_injective :
    Function.Injective (fun x : L₀ ⧸ Ideal.span {g₀} ↦ (p : L₀ ⧸ Ideal.span {g₀}) * x) := by
  have hpL : IsSMulRegular L₀ (p : L₀) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    simpa only [map_natCast] using h
  have h := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod L₀ (p : L₀) g₀ hpL
    (deltaPDivisionFirstRelation_mod_p_isSMulRegular D y s hpA hy)
  exact Eq.mp (congrArg (fun c : L₀ ⧸ Ideal.span {g₀} ↦
    IsSMulRegular (L₀ ⧸ Ideal.span {g₀}) c)
      (map_natCast (Ideal.Quotient.mk (Ideal.span {g₀})) p)) h

/-- pと最初の実p除算関係は自由環上の弱正則対。 -/
theorem deltaPDivisionFirstRelation_pair_isWeaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular L₀ [(p : L₀), g₀] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨?_, ?_⟩
  · have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    simpa only [map_natCast] using h
  · let e := Submodule.quotEquivOfEq
      ((p : L₀) • (⊤ : Submodule L₀ L₀))
      (Ideal.span {(p : L₀)} : Submodule L₀ L₀)
      (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
    apply (e.isSMulRegular_congr _).mpr
    exact (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp
      (deltaPDivisionFirstRelation_mod_p_isSMulRegular D y s hpA hy)

/-- 実対(p,g_s)のKoszul複体は対応する通常商の分解。 -/
theorem deltaPDivisionFirstRelation_pair_isKoszulResolution :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin 2 ↦ if i = 0 then (p : L₀) else g₀) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa [List.ofFn_succ] using deltaPDivisionFirstRelation_pair_isWeaklyRegular D y s hpA hy

end SerrePositivity.BhattScholze
