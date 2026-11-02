module

public import SerrePositivity.CLMST.CompletedSourceLength
public import SerrePositivity.CLMST.PerfectoidCokernelEuler
public import SerrePositivity.LengthAlgebra.KoszulModule

/-! # 完備テンソル代数の余核の有限性と Euler 消去

比較元の長さの有限性を有限段から実際に供給する。
比較先の負次数の長さが有限なら、短完全列から余核の負次数も有限となる。
さらに最後の元の所属と実際の零化冪から、共通の Euler 消去を適用する。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory
attribute [local instance] HasDerivedCategory.standard

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- 比較先の負次数の有限性から、有限段の列について実際の余核の負次数も有限になる。 -/
theorem completedTensor_stage_cokernel_negative_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A)
    (hinj : Function.Injective (toMixedPerfectoid A D t p hperf))
    (n : ℕ) {r : ℕ} (z : Fin r → Section2.StageAlgebra A D t p n)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical)
    (hC : ∀ q : ℤ, q < 0 → (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) ≠ ⊤)
    (q : ℤ) (hq : q < 0) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          (AlgebraMapCokernel ((CompletedTower A t p) ⊗[A] D)
            (RPerfd A D t p hperf)))).homology q) ≠ ⊤ :=
  lambdaKoszul_algebraMap_cokernel_ne_top (completedTensorLength A D t p ht)
    (RPerfd A D t p hperf) hinj (completedTensorMaxIdeal_fg A D t p)
    ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z) hJ q (hC q hq)
    (completedTensor_stage_koszul_length_ne_top A D t p ht hp n z hJ (q + 1))

/-- 比較先の負次数の有限性、零化冪、最後の元の所属から余核の Euler 評価を消す。
比較元・余核の長さの有限性を独立の未知の仮定として要求しない。 -/
theorem completedTensor_stage_cokernel_euler_eq_zero
    (hp : (p : A) ∈ maximalIdeal A)
    (hinj : Function.Injective (toMixedPerfectoid A D t p hperf))
    (n : ℕ) {r : ℕ} (z : Fin (r + 1) → Section2.StageAlgebra A D t p n)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical)
    (g : CompletedTower A t p) (N : ℕ)
    (hN : ∀ x : (RPerfd A D t p hperf) ⧸
      (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
        ((CompletedTower A t p) ⊗[A] D) p hperf).range, g ^ N • x = 0)
    (hz : Section2.stageToCompletedTensor A D t p n (z (Fin.last r)) ∈
      Ideal.span (Set.range (Fin.init ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))) ⊔
        Ideal.span {(algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) g) ^ N})
    (hC : ∀ q : ℤ, q < 0 → (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) ≠ ⊤) :
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          (AlgebraMapCokernel ((CompletedTower A t p) ⊗[A] D)
            (RPerfd A D t p hperf)))) = 0 :=
  perfectoidizationCokernel_euler_eq_zero (CompletedTower A t p)
    ((CompletedTower A t p) ⊗[A] D) p hperf (completedTensorLength A D t p ht)
    (completedTensorMaxIdeal_fg A D t p) g N hN
    ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z) hJ hz
    (completedTensor_stage_cokernel_negative_length_ne_top A D t p ht hperf
      hp hinj n z hJ hC)

/-- 余核の全長さの有限性も最後の元の所属から導き、実際の二つの Euler 評価を比較する。 -/
theorem completedTensor_stage_euler_comparison
    (hp : (p : A) ∈ maximalIdeal A)
    (hinj : Function.Injective (toMixedPerfectoid A D t p hperf))
    (n : ℕ) {r : ℕ} (z : Fin (r + 1) → Section2.StageAlgebra A D t p n)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical)
    (g : CompletedTower A t p) (N : ℕ)
    (hN : ∀ x : (RPerfd A D t p hperf) ⧸
      (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
        ((CompletedTower A t p) ⊗[A] D) p hperf).range, g ^ N • x = 0)
    (hz : Section2.stageToCompletedTensor A D t p n (z (Fin.last r)) ∈
      Ideal.span (Set.range (Fin.init ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))) ⊔
        Ideal.span {(algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) g) ^ N})
    (hC : ∀ q : ℤ, q < 0 → (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) ≠ ⊤) :
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))) =
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) := by
  let R := CompletedTower A t p
  let S := R ⊗[A] D
  let y := (Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z
  let lam := completedTensorLength A D t p ht
  have lNegative := completedTensor_stage_cokernel_negative_length_ne_top
    A D t p ht hperf hp hinj n z hJ hC
  have lQ := lambdaHomology_koszulModule_ne_top_of_last_mem_span_sup lam y
    (ModuleCat.of S (PerfectoidizationCokernel R S p hperf)) ((algebraMap R S g) ^ N)
    (perfectoidizationCokernel_annihilated R S p hperf g N hN) hz
    (isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p) y hJ _)
    lNegative
  exact lambdaKoszul_algebraMap_euler_eq_of_cokernel_euler_zero lam
    (RPerfd A D t p hperf) hinj (completedTensorMaxIdeal_fg A D t p) y hJ
    (completedTensor_stage_koszul_length_ne_top A D t p ht hp n z hJ) lQ
    (completedTensor_stage_cokernel_euler_eq_zero A D t p ht hperf
      hp hinj n z hJ g N hN hz hC)

end SerrePositivity.CLMST
