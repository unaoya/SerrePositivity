module

public import SerrePositivity.LengthAlgebra.HomologyExactBounds
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl
public import SerrePositivity.CommutativeAlgebra.AlgebraMapCokernel
public import SerrePositivity.PerfectComplex.NormalizedEuler

/-! # 単射な代数写像の Koszul ホモロジーの長さの誤差評価

余核を係数とする Koszul 複体の隣接次数の長さで、両方向の誤差を抑える。
列のイデアルへの台の条件から、長さの加法性に必要な冪ねじれ性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {S : Type u} [CommRing S] {J : Ideal S} (lam : NormalizedLength S J)

/-- 係数加群に依存せず、台の条件から Koszul ホモロジーの冪ねじれ性を供給する。 -/
theorem isPowTorsion_koszulModuleHomology (hfg : J.FG) {e : ℕ} (z : Fin e → S)
    (hJ : J ≤ (Ideal.span (Set.range z)).radical) (M : ModuleCat.{u} S) (q : ℤ) :
    IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q) :=
  supported_homology_isPowTorsion hfg hJ
    (isSupported_koszulComplexOn z ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) q

/-- 比較する二つの Koszul ホモロジーの長さを、余核の長さで両方向から抑える。
値は ℝ≥0∞。Noether 性、有限長、余核の長さ零を要求しない。 -/
theorem lambdaKoszul_algebraMap_cokernel_bounds
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical) (q : ℤ) :
    (lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) ≤
      lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) +
      lam.len (((koszulModuleFunctor z).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))).homology q)) ∧
    (lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) ≤
      lam.len (((koszulModuleFunctor z).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))).homology (q - 1)) +
      lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q)) := by
  let sc := (algebraMapCokernelShortComplex S C).map (koszulModuleFunctor z)
  have hs := koszulModuleFunctor_shortExact z (algebraMapCokernelShortComplex S C)
    (algebraMapCokernelShortComplex_shortExact S C hinj)
  have ht₁ := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S S) q
  have ht₂ := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S C) q
  have ht₃ := isPowTorsion_koszulModuleHomology hfg z hJ
    (ModuleCat.of S (AlgebraMapCokernel S C)) q
  have htprev := isPowTorsion_koszulModuleHomology hfg z hJ
    (ModuleCat.of S (AlgebraMapCokernel S C)) (q - 1)
  exact ⟨lambdaHomology_shortExact_le lam sc hs q ht₁ ht₂ ht₃,
    lambdaHomology_shortExact_left_le lam sc hs q htprev ht₁ ht₂⟩

/-- 余核の隣接する二次数の長さが零なら、比較する Koszul ホモロジーの長さは一致。 -/
theorem lambdaKoszul_algebraMap_eq_of_cokernel_length_zero
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical) (q : ℤ)
    (hprev : lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology (q - 1)) = 0)
    (hcurrent : lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) = 0) :
    lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) =
      lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) := by
  have hb := lambdaKoszul_algebraMap_cokernel_bounds lam C hinj hfg z hJ q
  apply le_antisymm
  · simpa only [hprev, zero_add] using hb.2
  · simpa only [hcurrent, add_zero] using hb.1

/-- 比較先の同次数と比較元の次次数が有限なら、余核の Koszul 長も有限。 -/
theorem lambdaKoszul_algebraMap_cokernel_ne_top
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical) (q : ℤ)
    (hC : lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) ≠ ⊤)
    (hSnext : lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology (q + 1)) ≠ ⊤) :
    lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) ≠ ⊤ := by
  let sc := (algebraMapCokernelShortComplex S C).map (koszulModuleFunctor z)
  have hs := koszulModuleFunctor_shortExact z (algebraMapCokernelShortComplex S C)
    (algebraMapCokernelShortComplex_shortExact S C hinj)
  exact lambdaHomology_shortExact_right_ne_top lam sc hs q
    (isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S C) q)
    (isPowTorsion_koszulModuleHomology hfg z hJ
      (ModuleCat.of S (AlgebraMapCokernel S C)) q)
    (isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S S) (q + 1)) hC hSnext

end SerrePositivity
