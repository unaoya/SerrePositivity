module

public import SerrePositivity.LengthAlgebra.PerfectBaseChange
public import SerrePositivity.LengthAlgebra.Ordinary

/-! # 旧有限自由 K₀ 評価と共通 Euler 評価の一致

数値の一致を K₀ 上の準同型の一致として述べる。
既存の公開定義と有限性の仮定を保ち、共通理論からの引き戻しと同定する。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits IsLocalRing

set_option backward.isDefEq.respectTransparency false in
/-- 通常の有限自由 K₀ 評価は、有限射影圏の共通 Euler 評価の引き戻しである。
局所性や正則性は必要なく、パラメータ商の Artin 性から Koszul 有限性を得る。 -/
theorem perfectEulerK0_ordinary_comp_freeToPerfectK0
    {R : Type u} [CommRing R] [IsNoetherianRing R] {e : ℕ} (z : Fin e → R)
    [IsArtinianRing (R ⧸ Ideal.span (Set.range z))] :
    (perfectEulerK0 (NormalizedLength.ordinary R) (Submodule.fg_bot) z bot_le
      (fun v _ q ↦ ordinary_koszul_pow_finite z v q)).comp freeToPerfectK0 =
        chiOrdHom z := by
  apply K0.hom_ext
  intro P
  simp only [AddMonoidHom.comp_apply, freeToPerfectK0_mk, perfectEulerK0_mk, chiOrdHom_mk]
  rw [perfectEuler_eq_lambdaEuler, chiOrd_eq_lambdaEuler_ordinary]
  rfl

/-- 旧 `chiLamHom_of_finite` は、新しい係数変更 Euler 評価と同じ準同型である。
旧 API の有限性証明 `hfinite` の選択には依存しない。 -/
theorem freeBaseChangeEulerK0_eq_chiLamHom_of_finite
    {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing T] [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C]
    [IsScalarTower A T C] {e : ℕ} (z : Fin e → A)
    (lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)))
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap T C ∘ (algebraMap A T ∘ z)))).radical)
    (hfin : KoszulFinite lam (algebraMap T C ∘ (algebraMap A T ∘ z)))
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) :
    freeBaseChangeEulerK0 (algebraMap T C) lam
      ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
      (algebraMap A T ∘ z) hJ hfin = chiLamHom_of_finite hz hfinite := by
  apply K0.hom_ext
  intro P
  simp only [freeBaseChangeEulerK0_mk, chiLamHom_of_finite_mk]

end SerrePositivity.LengthAlgebra
