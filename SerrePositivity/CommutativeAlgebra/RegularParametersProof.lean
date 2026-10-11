module

public import SerrePositivity.CommutativeAlgebra.RegularLocalQuotient
public import SerrePositivity.CommutativeAlgebra.RegularGradedPresentation
public import Mathlib.Data.List.OfFn

/-! # 次元と同数の極大イデアル生成元の正則列性

最小生成元の正則性と、その先頭による商の正則局所性を使って、生成族の長さに
関する帰納法を行う。商の上の正則性を元の環の加群の正則性へ係数制限して戻す。
-/

@[expose] public section

universe u

open IsLocalRing RingTheory.Sequence

namespace SerrePositivity

/-- 全ての Noether 局所環について、次元と同数の極大イデアル生成元の先頭が正則なら、
その生成列は弱正則列である。長さに関する帰納法の接続を独立に述べる。 -/
theorem isWeaklyRegular_of_generator_regularity
    (hregular : ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
      {s : ℕ} (y : Fin (s + 1) → S),
      Ideal.span (Set.range y) = maximalIdeal S →
      ringKrullDim S = s + 1 → IsSMulRegular S (y 0))
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {e : ℕ} (z : Fin e → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (he : ringKrullDim R = e) : IsWeaklyRegular R (List.ofFn z) := by
  induction e generalizing R with
  | zero => simp
  | succ e ih =>
      have he' : ringKrullDim R = e + 1 := by simpa only [Nat.cast_succ] using he
      have hhead := hregular R z hz he'
      obtain ⟨hquotient, hdim⟩ :=
        RegularLocalQuotient.isRegularLocalRing_quotient_head_and_dim z hz he'
      let : IsRegularLocalRing (R ⧸ Ideal.span {z 0}) := hquotient
      let q := Ideal.Quotient.mk (Ideal.span {z 0})
      have hgen : Ideal.span (Set.range (fun i : Fin e ↦ q (z i.succ))) =
          maximalIdeal (R ⧸ Ideal.span {z 0}) :=
        RegularLocalQuotient.span_tail_quotient_eq_maximalIdeal z hz
      have htail : IsWeaklyRegular (R ⧸ Ideal.span {z 0})
          (List.ofFn (fun i : Fin e ↦ q (z i.succ))) :=
        ih _ _ hgen hdim
      have hmap : List.ofFn (fun i : Fin e ↦ q (z i.succ)) =
          (List.ofFn (Fin.tail z)).map (algebraMap R (R ⧸ Ideal.span {z 0})) := by
        rw [List.map_ofFn]
        rfl
      rw [hmap] at htail
      have htailR : IsWeaklyRegular (R ⧸ Ideal.span {z 0}) (List.ofFn (Fin.tail z)) :=
        (isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {z 0})
          (R ⧸ Ideal.span {z 0}) (List.ofFn (Fin.tail z))).mp htail
      let equiv : QuotSMulTop (z 0) R ≃ₗ[R] R ⧸ Ideal.span {z 0} :=
        Submodule.quotEquivOfEq _ _ (by
          rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
      rw [List.ofFn_succ]
      exact (isWeaklyRegular_cons_iff R (z 0) (List.ofFn (Fin.tail z))).mpr
        ⟨hhead, (equiv.isWeaklyRegular_congr (List.ofFn (Fin.tail z))).mpr htailR⟩

/-- 正則局所環で、次元と同数の極大イデアル生成元は弱正則列をなす。
各生成元の正則性は随伴次数環と Samuel 次元定理から導く。 -/
theorem isWeaklyRegular_of_minimal_generators (R : Type u) [CommRing R]
    [IsRegularLocalRing R] {e : ℕ} (z : Fin e → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) (he : ringKrullDim R = e) :
    IsWeaklyRegular R (List.ofFn z) := by
  apply isWeaklyRegular_of_generator_regularity ?_ R z hz he
  intro S _ _ _ s y hy hd
  exact HilbertSamuel.isSMulRegular_generator_of_span_eq_maximalIdeal S y hy hd 0

end SerrePositivity
