module

public import SerrePositivity.CLMST.CompletedCokernelFiniteEuler
public import SerrePositivity.CLMST.NormalizedAlmostLength
public import SerrePositivity.CLMST.CohomologyVanishing
public import SerrePositivity.LengthAlgebra.KoszulRestriction

/-! # perfectoid 化を係数とする Koszul ホモロジーの長さ消滅

有限段の任意のパラメータ系について、Corollary 4.0.4 の almost 消滅を
Proposition 4.0.10 の長さ消滅へ接続する。テンソル代数を底環とする係数加群の
Koszul モデルと perfectoid 化上のモデルは、係数制限の実際の同型で比較する。
この接続に新しい引用は加えない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory
set_option backward.isDefEq.respectTransparency true

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 有限段の全パラメータ系について、perfectoid 化を係数とする負次数の長さは零。
外部依存は既存の Corollary 4.0.4 と巡回評価 Proposition 4.0.10 である。 -/
theorem completedTensor_stage_target_koszul_length_eq_zero
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) (y : Fin h → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y)
    (q : ℤ) (hq : q < 0) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) = 0 := by
  let : IsLocalRing (StageAlgebra A D t p n) :=
    stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  let S := (CompletedTower A t p) ⊗[A] D
  let C := RPerfd A D t p hperf
  let z := (stageToCompletedTensor A D t p n).toRingHom ∘ y
  let i : ℕ := (-q).toNat
  have hi : 0 < i := by dsimp [i]; omega
  have hqi : q = -(i : ℤ) := by dsimp [i]; omega
  have hseq : algebraMap S C ∘ z = fun j ↦ toRPerfd A D t p hperf n (y j) := by
    funext j
    change toMixedPerfectoid A D t p hperf (stageToCompletedTensor A D t p n (y j)) = _
    exact stageToCompletedTensor_toMixedPerfectoid A D t p hperf n (y j)
  have hann :
      let _ := Module.compHom ((koszulComplex (algebraMap S C ∘ z)).homology q)
        (algebraMap (CompletedTower A t p) C)
      Almost.IsAlmostZero
        (perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g))
        ((koszulComplex (algebraMap S C ∘ z)).homology q) := by
    rw [hseq, hqi]
    exact (Inputs.corollary_4_0_4 A D hinj hres t hdimA hdimD hpos ht hsop
      p htp e he hperf g hg hEtale).2 n y hy i hi
  let H := (koszulComplex (algebraMap S C ∘ z)).homology q
  let := Module.compHom H (algebraMap (CompletedTower A t p) C)
  have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
    (by
      rw [IsScalarTower.algebraMap_eq A D (StageAlgebra A D t p n)]
      exact (stageAlgebra_algebraMap_injective A D t p n).comp hinj) y hy
  have htorS := isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
    z hJ (ModuleCat.of S C) q
  have htor : IsPowTorsion (completedTowerMaxIdeal A t p) H := by
    let X := ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q
    have hmap : (completedTowerMaxIdeal A t p).map (algebraMap (CompletedTower A t p) S) ≤
        completedTensorMaxIdeal A D t p := by
      dsimp [completedTowerMaxIdeal, completedTensorMaxIdeal]
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have hX := IsPowTorsion.comap (algebraMap (CompletedTower A t p) S) hmap X htorS
    let iso : (ModuleCat.restrictScalars (algebraMap (CompletedTower A t p) S)).obj X ≅
        (ModuleCat.restrictScalars (algebraMap (CompletedTower A t p) C)).obj H :=
      (ModuleCat.restrictScalars (algebraMap (CompletedTower A t p) S)).mapIso
        (koszulModuleAlgebraHomologyIso z q) ≪≫
      (ModuleCat.restrictScalarsComp'App (algebraMap (CompletedTower A t p) S)
        (algebraMap S C) (algebraMap (CompletedTower A t p) C)
        (IsScalarTower.algebraMap_eq (CompletedTower A t p) S C) H).symm
    exact IsPowTorsion.of_equiv iso.toLinearEquiv hX
  have hzero := completedLength_eq_zero_of_perfectoidIdeal_annihilates
    A (ResidueField D) p t hpos htp ht hdimA e he hperf g hg H htor hann
  change (completedTensorLength A D t p _).len
    (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) = 0
  rw [completedTensorLength, length_comap_koszulModuleHomology]
  exact hzero

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- パラメータ系の引用から比較先の有限性を供給し、余核の Euler 消滅と二つの Euler 評価の一致へ接続。
零化冪と最後の元の所属だけは、適用する具体的な列について明示的に受け取る。 -/
theorem completedTensor_stage_parameter_euler_comparison
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y)
    (b : CompletedTower A t p) (N : ℕ)
    (hN : ∀ x : (RPerfd A D t p hperf) ⧸
      (perfectoidizationModuleMap (CompletedTower A t p)
        ((CompletedTower A t p) ⊗[A] D) p hperf).range, b ^ N • x = 0)
    (hyLast : stageToCompletedTensor A D t p n (y (Fin.last r)) ∈
      Ideal.span (Set.range (Fin.init ((stageToCompletedTensor A D t p n).toRingHom ∘ y))) ⊔
        Ideal.span {(algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) b) ^ N}) :
    let lam := completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
    let z := (stageToCompletedTensor A D t p n).toRingHom ∘ y
    let S := (CompletedTower A t p) ⊗[A] D
    let C := RPerfd A D t p hperf
    (lambdaEuler lam ((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))) = 0) ∧
    (lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
      lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S))) := by
  subst h
  let : IsLocalRing (StageAlgebra A D t p n) :=
    stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp, ← ht]
    exact Ideal.subset_span (Set.mem_range_self _)
  have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
    (by
      rw [IsScalarTower.algebraMap_eq A D (StageAlgebra A D t p n)]
      exact (stageAlgebra_algebraMap_injective A D t p n).comp hinj) y hy
  have hinjC := toMixedPerfectoid_injective_of_domain A D t p hperf hinj g hg hEtale
  have hC : ∀ q : ℤ, q < 0 →
      (completedTensorLength A D t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
        (((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
          (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
            (RPerfd A D t p hperf))).homology q) ≠ ⊤ := by
    intro q hq
    rw [completedTensor_stage_target_koszul_length_eq_zero A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf g hg hEtale n y hy q hq]
    exact ENNReal.zero_ne_top
  exact ⟨completedTensor_stage_cokernel_euler_eq_zero
    A D t p _ hperf hp hinjC n y hJ b N hN hyLast hC,
    completedTensor_stage_euler_comparison A D t p _ hperf hp hinjC n y hJ b N hN hyLast hC⟩

end SerrePositivity.CLMST
