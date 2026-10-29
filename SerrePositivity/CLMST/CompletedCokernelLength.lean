module

public import SerrePositivity.CLMST.CompletedTensorIsogeny
public import SerrePositivity.CLMST.PerfectoidCokernel
public import SerrePositivity.LengthAlgebra.KoszulCokernelBounds
public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedFiniteLength
public import SerrePositivity.CommutativeAlgebra.RootTower.Restriction
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic

/-! # 完備テンソル代数と perfectoid 化の Koszul 長さの誤差評価

完備塔の長さをテンソル代数へ係数制限し、余核の隣接次数の長さで比較を抑える。
パラメータ系から長さの加法性に必要な台・冪ねじれ性を確認する。
余核の長さ零は、この評価から別の工程として残す。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

/-- テンソル代数に拡張した基底の極大イデアル。 -/
def completedTensorMaxIdeal : Ideal ((CompletedTower A t p) ⊗[A] D) :=
  (maximalIdeal A).map (algebraMap A ((CompletedTower A t p) ⊗[A] D))

/-- 完備塔の正規化長さをテンソル代数上の加群へ係数制限する。 -/
def completedTensorLength : NormalizedLength ((CompletedTower A t p) ⊗[A] D)
    (completedTensorMaxIdeal A D t p) :=
  (RootTowerLength.completedNormalizedLength A t p ht).comap
    (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D))
    (completedTensorMaxIdeal A D t p) (by
      dsimp only [completedTowerMaxIdeal, completedTensorMaxIdeal]
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])

omit [Fact p.Prime] in
/-- 長さの加法性のイデアルは、基底のNoether性から有限生成。 -/
theorem completedTensorMaxIdeal_fg : (completedTensorMaxIdeal A D t p).FG :=
  (maximalIdeal A).fg_of_isNoetherianRing.map _

omit [IsNoetherianRing A] [Fact p.Prime] in
/-- Dのパラメータ系をテンソル代数へ写すと、長さの定義域の台の条件を満たす。 -/
theorem completedTensorMaxIdeal_le_parameter_radical
    [IsLocalRing D] [Module.Finite A D] (hinj : Function.Injective (algebraMap A D))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range (Algebra.TensorProduct.includeRight.toRingHom ∘ z))).radical := by
  let φ : D →+* (CompletedTower A t p) ⊗[A] D := Algebra.TensorProduct.includeRight.toRingHom
  have hc : φ.comp (algebraMap A D) = algebraMap A ((CompletedTower A t p) ⊗[A] D) := by
    ext a
    exact Algebra.TensorProduct.includeRight.commutes a
  have hm := Ideal.map_mono (f := φ) (maximalIdeal_map_le_of_finite_of_injective A D hinj)
  rw [Ideal.map_map, hc] at hm
  dsimp only [completedTensorMaxIdeal]
  apply hm.trans
  rw [← hz.2]
  have hr : (Ideal.span (Set.range z)).radical.map φ ≤
      ((Ideal.span (Set.range z)).map φ).radical := Ideal.map_radical_le φ
  convert hr using 1
  rw [Ideal.map_span, ← Set.range_comp]

/-- 具体的な正規化長さで、perfectoid化のホモロジーの長さを余核によって両方向から抑える。 -/
theorem completedTensor_parameter_koszul_length_bounds
    [IsLocalRing D] [Module.Finite A D] [IsDomain D] [CharZero D]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hinj : Function.Injective (algebraMap A D)) (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (q : ℤ) :
    let S := (CompletedTower A t p) ⊗[A] D
    let y := Algebra.TensorProduct.includeRight.toRingHom ∘ z
    let lam := completedTensorLength A D t p ht
    let C := RPerfd A D t p hperf
    (lam.len (((koszulModuleFunctor y).obj (ModuleCat.of S C)).homology q) ≤
      lam.len (((koszulModuleFunctor y).obj (ModuleCat.of S S)).homology q) +
      lam.len (((koszulModuleFunctor y).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))).homology q)) ∧
    (lam.len (((koszulModuleFunctor y).obj (ModuleCat.of S S)).homology q) ≤
      lam.len (((koszulModuleFunctor y).obj
        (ModuleCat.of S (AlgebraMapCokernel S C))).homology (q - 1)) +
      lam.len (((koszulModuleFunctor y).obj (ModuleCat.of S C)).homology q)) := by
  let : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D
  exact lambdaKoszul_algebraMap_cokernel_bounds (completedTensorLength A D t p ht)
    (RPerfd A D t p hperf) (toMixedPerfectoid_injective_of_domain A D t p hperf hinj g hg hEtale)
    (completedTensorMaxIdeal_fg A D t p)
    (Algebra.TensorProduct.includeRight.toRingHom ∘ z)
    (completedTensorMaxIdeal_le_parameter_radical A D t p hinj z hz) q

/-- 具体的な長さについて、比較先の同次数と比較元の次次数から余核の有限性を導く。 -/
theorem completedTensor_parameter_cokernel_length_ne_top
    [IsLocalRing D] [Module.Finite A D] [IsDomain D] [CharZero D]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hinj : Function.Injective (algebraMap A D)) (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (q : ℤ)
    (hC : (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) ≠ ⊤)
    (hSnext : (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology (q + 1)) ≠ ⊤) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          (AlgebraMapCokernel ((CompletedTower A t p) ⊗[A] D)
            (RPerfd A D t p hperf)))).homology q) ≠ ⊤ := by
  let : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D
  exact lambdaKoszul_algebraMap_cokernel_ne_top (completedTensorLength A D t p ht)
    (RPerfd A D t p hperf) (toMixedPerfectoid_injective_of_domain A D t p hperf hinj g hg hEtale)
    (completedTensorMaxIdeal_fg A D t p)
    (Algebra.TensorProduct.includeRight.toRingHom ∘ z)
    (completedTensorMaxIdeal_le_parameter_radical A D t p hinj z hz) q hC hSnext

/-- 完備塔上で有限生成な冪ねじれ加群なら、具体的なテンソル代数の長さも有限。
有限生成性を完備塔上の構造条件として使い、その環のNoether性は要求しない。 -/
theorem completedTensorLength_ne_top_of_finite
    (hp : (p : A) ∈ maximalIdeal A)
    (M : Type u) [AddCommGroup M] [Module ((CompletedTower A t p) ⊗[A] D) M]
    (hfinite :
      let _ := Module.compHom M
        (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D))
      Module.Finite (CompletedTower A t p) M)
    (hM : IsPowTorsion (completedTensorMaxIdeal A D t p) M) :
    (completedTensorLength A D t p ht).len M ≠ ⊤ := by
  let := Module.compHom M (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D))
  let : Module.Finite (CompletedTower A t p) M := hfinite
  have htM : IsPowTorsion (completedTowerMaxIdeal A t p) M :=
    IsPowTorsion.comap (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D))
      (by
        dsimp only [completedTowerMaxIdeal, completedTensorMaxIdeal]
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]) M hM
  exact RootTowerLength.completedNormalizedLength_ne_top_of_finite A t p ht hp M htM

end SerrePositivity.CLMST
