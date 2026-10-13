module

public import SerrePositivity.CommutativeAlgebra.GradedReesNoetherian

/-! # イデアルの初期形式の有限な持ち上げ

元の環のイデアルJの元を係数に持つRees多項式のイデアルを作る。
その随伴次数環での像の有限生成元を、実際にJの係数を持つ有限個の多項式へ持ち上げる。
元の環のNoether性は仮定しない。次数付き近似への変換は別の課題。
-/

@[expose] public section
universe u
namespace SerrePositivity.HilbertSamuel
variable (R : Type u) [CommRing R] (I J : Ideal R)

/-- Jの元を全係数に持つRees多項式のイデアル。 -/
def reesCoefficientIdeal : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : Polynomial R).coeff n ∈ J}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro p q hp hq n
    change ((p : Polynomial R) + (q : Polynomial R)).coeff n ∈ J
    rw [Polynomial.coeff_add]
    exact J.add_mem (hp n) (hq n)
  smul_mem' := by
    intro a p hp n
    change ((a : Polynomial R) * (p : Polynomial R)).coeff n ∈ J
    rw [Polynomial.coeff_mul]
    exact J.sum_mem (fun ij _ ↦ J.mul_mem_left _ (hp ij.2))

/-- 初期形式に対応する単項式は、元のイデアルの係数を持つ。 -/
theorem monomial_mem_reesCoefficientIdeal (n : ℕ) (x : R) (hxI : x ∈ I ^ n) (hxJ : x ∈ J) :
    (⟨Polynomial.monomial n x, reesAlgebra.monomial_mem.mpr hxI⟩ : reesAlgebra I) ∈
      reesCoefficientIdeal R I J := by
  intro k
  change (Polynomial.monomial n x).coeff k ∈ J
  rw [Polynomial.coeff_monomial]
  split_ifs
  · exact hxJ
  · exact J.zero_mem

/-- 初期形式の像を生成する有限列を、Jの係数を持つRees多項式へ実際に持ち上げる。 -/
theorem exists_finite_reesCoefficientIdeal_lifts (hI : I.FG) [IsNoetherianRing (R ⧸ I)] :
    ∃ n : ℕ, ∃ z : Fin n → reesAlgebra I,
      (∀ i k, (z i : Polynomial R).coeff k ∈ J) ∧
      Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk
        (I.map (algebraMap R (reesAlgebra I))) (z i))) =
      (reesCoefficientIdeal R I J).map
        (Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))) := by
  classical
  let : IsNoetherianRing (GradedReesRing R I) := isNoetherianRing_gradedReesRing_of_fg R I hI
  let f := Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))
  let L := (reesCoefficientIdeal R I J).map f
  obtain ⟨n, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp L.fg_of_isNoetherianRing
  have hlift (i : Fin n) : ∃ x : reesAlgebra I, x ∈ reesCoefficientIdeal R I J ∧ f x = y i := by
    apply (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp
    change y i ∈ L
    rw [← hy]
    exact Ideal.subset_span (Set.mem_range_self i)
  choose z hz hf using hlift
  refine ⟨n, z, (fun i k ↦ hz i k), ?_⟩
  have hfun : (fun i ↦ f (z i)) = y := funext hf
  change Ideal.span (Set.range (fun i ↦ f (z i))) = L
  rw [hfun]
  exact hy

end SerrePositivity.HilbertSamuel
