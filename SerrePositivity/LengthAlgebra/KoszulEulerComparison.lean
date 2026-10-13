module

public import SerrePositivity.LengthAlgebra.ShortExactEuler
public import SerrePositivity.LengthAlgebra.KoszulCokernelBounds
public import SerrePositivity.HomologicalAlgebra.KoszulModuleBounds
public import SerrePositivity.LengthAlgebra.KoszulErrorEuler

/-! # 余核の Euler 消去による Koszul 比較

短完全列から比較先の全次数の長さの有限性を導き、
共通の Euler 加法性と余核側の Euler 評価零から比較を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {S : Type u} [CommRing S] {J : Ideal S} (lam : NormalizedLength S J)

/-- 余核の負次数の有限性と最後の元の所属から、比較先の零次数を含む全長さも有限になる。 -/
theorem lambdaKoszul_algebraMap_target_ne_top_of_last_mem_span_sup
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin (e + 1) → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
    (a : S) (ha : ∀ m : AlgebraMapCokernel S C, a • m = 0)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔ Ideal.span {a})
    (lS : ∀ q, lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) ≠ ⊤)
    (lNegative : ∀ q : ℤ, q < 0 → lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) ≠ ⊤)
    (q : ℤ) :
    lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) ≠ ⊤ := by
  have lQ := lambdaHomology_koszulModule_ne_top_of_last_mem_span_sup lam z
    (ModuleCat.of S (AlgebraMapCokernel S C)) a ha hz
    (isPowTorsion_koszulModuleHomology hfg z hJ _) lNegative
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨lS q, lQ q⟩)
    (lambdaKoszul_algebraMap_cokernel_bounds lam C hinj hfg z hJ q).1

/-- 比較元と余核の全長さが有限で、余核の Euler 評価が零なら、二つの Euler 評価は一致する。 -/
theorem lambdaKoszul_algebraMap_euler_eq_of_cokernel_euler_zero
    (C : Type u) [CommRing C] [Algebra S C]
    (hinj : Function.Injective (algebraMap S C)) (hfg : J.FG)
    {e : ℕ} (z : Fin e → S) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
    (lS : ∀ q, lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S S)).homology q) ≠ ⊤)
    (lQ : ∀ q, lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))).homology q) ≠ ⊤)
    (hQ : lambdaEuler lam ((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))) = 0) :
    lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
      lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S)) := by
  let sc := (algebraMapCokernelShortComplex S C).map (koszulModuleFunctor z)
  have hs := koszulModuleFunctor_shortExact z (algebraMapCokernelShortComplex S C)
    (algebraMapCokernelShortComplex_shortExact S C hinj)
  have tS := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S S)
  have tC := isPowTorsion_koszulModuleHomology hfg z hJ (ModuleCat.of S C)
  have tQ := isPowTorsion_koszulModuleHomology hfg z hJ
    (ModuleCat.of S (AlgebraMapCokernel S C))
  have lC (q : ℤ) : lam.len (sc.X₂.homology q) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨lS q, lQ q⟩)
      (lambdaHomology_shortExact_le lam sc hs q (tS q) (tC q) (tQ q))
  have he := lambdaEuler_shortExact lam sc hs
    (koszulModuleFunctor_bounded z (ModuleCat.of S C))
    (koszulModuleFunctor_bounded z (ModuleCat.of S (AlgebraMapCokernel S C)))
    tS tC tQ lS lC lQ
  change lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
    lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S)) +
      lambdaEuler lam ((koszulModuleFunctor z).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))) at he
  simpa only [hQ, add_zero] using he

end SerrePositivity
