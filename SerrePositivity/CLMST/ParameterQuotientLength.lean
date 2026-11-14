module

public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Consequences
public import SerrePositivity.CommutativeAlgebra.AlgebraMapCokernel
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import SerrePositivity.LengthAlgebra.KoszulModule
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.CommutativeAlgebra.RootTower.BaseChange
public import SerrePositivity.HomologicalAlgebra.FlatKoszulFiniteness
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Formula
public import SerrePositivity.CommutativeAlgebra.Koszul.FiniteLength
public import SerrePositivity.CLMST.CyclicLengthBound
public import SerrePositivity.CLMST.KoszulAnnihilation
public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Generators

/-! # Prop 4.0.14：perfectoid 化のパラメータ商の長さ

## 概要

有限段 `D_n = A_n ⊗_A D` の任意のパラメータ系について、perfectoid 化の商の正規化長さが `p^(-nh)` 倍の Hilbert–Samuel 重複度に等しいことを示す。perfectoid 化の余核の Koszul ホモロジーの零化と Euler の消去、完備テンソル代数の Koszul 長さの誤差の評価、比較元の Euler 評価の有限段での計算、perfectoid 化を係数とする Koszul ホモロジーの長さの消滅（Cor 4.0.4 と Prop 4.0.10 の接続）、パラメータの選択による Euler の比較を組み合わせる。

## 方針

完備塔の長さをテンソル代数へ係数制限し、余核の隣接次数の長さで比較を抑える。平坦な基底変更で有限段へ戻し、共通の剰余体で通常の長さと一致させる。

## 規約

CLMST Prop 4.0.14。旧 `CLMST/PerfectoidCokernel`・`PerfectoidCokernelEuler`・`CompletedCokernelLength`・`CompletedCokernelFiniteEuler`・`CompletedSourceLength`・`SourceEulerEvaluation`・`CompletedTargetLength`・`SelectedParameterEuler`・`CompletedParameterFiniteness`。

## 使われ方

`ParameterPowerLength`。
-/

@[expose] public noncomputable section

universe u

section PerfectoidCokernelPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- perfectoid 化の標準写像の、元の代数 S 上の余核。 -/
abbrev PerfectoidizationCokernel := AlgebraMapCokernel S (Perfectoidization R S p hR)

/-- 原典の isogeny で制御した R 加群の余核との比較。 -/
def perfectoidizationCokernelRestrictEquiv :
    ((Perfectoidization R S p hR) ⧸ (BhattScholze.perfectoidizationModuleMap R S p hR).range) ≃ₗ[R]
      PerfectoidizationCokernel R S p hR :=
  algebraMapCokernelRestrictEquiv R S (Perfectoidization R S p hR)

/-- 原典の余核の零化を、S 加群としての余核へ移す。同じ冪を保持する。 -/
theorem perfectoidizationCokernel_annihilated (g : R) (N : ℕ)
    (h : ∀ x : (Perfectoidization R S p hR) ⧸ (BhattScholze.perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0) :
    ∀ x : PerfectoidizationCokernel R S p hR, (algebraMap R S g) ^ N • x = 0 := by
  simpa only [map_pow] using algebraMapCokernel_annihilated_algebraMap_of_restrict
    R S (Perfectoidization R S p hR) (g ^ N) h

/-- 任意の S の列と全次数に、余核と同じ消去冪を供給する。 -/
theorem perfectoidizationCokernel_koszul_annihilated (g : R) (N : ℕ)
    (h : ∀ x : (Perfectoidization R S p hR) ⧸ (BhattScholze.perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0) {e : ℕ} (z : Fin e → S) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj
      (ModuleCat.of S (PerfectoidizationCokernel R S p hR))).homology q,
      (algebraMap R S g) ^ N • x = 0 :=
  koszulModuleHomology_annihilated z (ModuleCat.of S (PerfectoidizationCokernel R S p hR))
    ((algebraMap R S g) ^ N) (perfectoidizationCokernel_annihilated R S p hR g N h) q

/-- S の任意の部分係数環に制限しても、同じ冪で Koszul ホモロジーを消せる。 -/
theorem perfectoidizationCokernel_restricted_koszul_annihilated
    {T : Type u} [CommRing T] (φ : T →+* S)
    (g : R) (a : T) (ha : φ a = algebraMap R S g) (N : ℕ)
    (h : ∀ x : (Perfectoidization R S p hR) ⧸ (BhattScholze.perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0) {e : ℕ} (z : Fin e → T) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj ((ModuleCat.restrictScalars φ).obj
      (ModuleCat.of S (PerfectoidizationCokernel R S p hR)))).homology q,
      a ^ N • x = 0 := by
  apply koszulModuleHomology_annihilated_restrictScalars φ
    (ModuleCat.of S (PerfectoidizationCokernel R S p hR)) z (a ^ N) ?_ q
  simpa only [map_pow, ha] using perfectoidizationCokernel_annihilated R S p hR g N h

/-- 単射性から、標準写像とS加群の余核の実際の短完全列が得られる。 -/
theorem perfectoidizationCokernel_shortExact
    (hinj : Function.Injective (BhattScholze.perfectoidizationModuleMap R S p hR)) :
    (algebraMapCokernelShortComplex S (Perfectoidization R S p hR)).ShortExact :=
  algebraMapCokernelShortComplex_shortExact S (Perfectoidization R S p hR) hinj

/-- 部分係数環への制限とKoszul構成の後も、同じ余核による短完全列が得られる。 -/
theorem perfectoidizationCokernel_restricted_koszul_shortExact
    {T : Type u} [CommRing T] (φ : T →+* S) {e : ℕ} (z : Fin e → T)
    (hinj : Function.Injective (BhattScholze.perfectoidizationModuleMap R S p hR)) :
    ((algebraMapCokernelShortComplex S (Perfectoidization R S p hR)).map
      (ModuleCat.restrictScalars φ ⋙ koszulModuleFunctor z)).ShortExact := by
  rw [ShortComplex.map_comp]
  exact koszulModuleFunctor_shortExact z _
    ((perfectoidizationCokernel_shortExact R S p hR hinj).map_of_exact
      (ModuleCat.restrictScalars φ))

end SerrePositivity.CLMST

end PerfectoidCokernelPart

section PerfectoidCokernelEulerPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 余核を係数とするKoszul複体のEuler評価を、実際の消去冪と所属条件から消す。 -/
theorem perfectoidizationCokernel_euler_eq_zero
    {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
    (g : R) (N : ℕ)
    (hN : ∀ x : (Perfectoidization R S p hR) ⧸ (BhattScholze.perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0)
    {e : ℕ} (z : Fin (e + 1) → S)
    (hJ : J ≤ (Ideal.span (Set.range z)).radical)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔
      Ideal.span {(algebraMap R S g) ^ N})
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj
        (ModuleCat.of S (PerfectoidizationCokernel R S p hR))).homology q) ≠ ⊤) :
    lambdaEuler lam ((koszulModuleFunctor z).obj
      (ModuleCat.of S (PerfectoidizationCokernel R S p hR))) = 0 :=
  lambdaEuler_koszulModule_eq_zero_of_last_mem_span_sup lam z
    (ModuleCat.of S (PerfectoidizationCokernel R S p hR)) ((algebraMap R S g) ^ N)
    (perfectoidizationCokernel_annihilated R S p hR g N hN) hz
    (isPowTorsion_koszulModuleHomology hfg z hJ _) lNegative

end SerrePositivity.CLMST

end PerfectoidCokernelEulerPart

section CompletedCokernelLengthPart

open scoped _root_.TensorProduct
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory
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

end CompletedCokernelLengthPart

section CompletedSourceLengthPart

open scoped _root_.TensorProduct
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

omit [IsNoetherianRing A] in
/-- 有限段のパラメータ系にも、標準段写像を通じて台の条件を供給する。 -/
theorem completedTensorMaxIdeal_le_stage_parameter_radical
    (n : ℕ) [IsLocalRing (Section2.StageAlgebra A D t p n)]
    (hinj : Function.Injective (algebraMap A (Section2.StageAlgebra A D t p n)))
    {r : ℕ} (z : Fin r → Section2.StageAlgebra A D t p n)
    (hz : IsSystemOfParameters (Section2.StageAlgebra A D t p n) z) :
    completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical := by
  let φ := (Section2.stageToCompletedTensor A D t p n).toRingHom
  have hc : φ.comp (algebraMap A (Section2.StageAlgebra A D t p n)) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) := by
    ext a
    exact (Section2.stageToCompletedTensor A D t p n).commutes a
  have hm := Ideal.map_mono (f := φ)
    (maximalIdeal_map_le_of_finite_of_injective A (Section2.StageAlgebra A D t p n) hinj)
  rw [Ideal.map_map, hc] at hm
  apply hm.trans
  rw [← hz.2]
  have hr : (Ideal.span (Set.range z)).radical.map φ ≤
      ((Ideal.span (Set.range z)).map φ).radical := Ideal.map_radical_le φ
  convert hr using 1
  rw [Ideal.map_span, ← Set.range_comp]

omit [IsLocalRing A] in
/-- 底環からの直接の基底変更でも、比較元の全次数の Koszul ホモロジーは完備塔上有限生成。 -/
theorem completedTensor_koszulModuleHomology_finite
    {r : ℕ} (z : Fin r → D) (q : ℤ) :
    let S := (CompletedTower A t p) ⊗[A] D
    let M := (((koszulModuleFunctor
      (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj (ModuleCat.of S S)).homology q)
    let _ := Module.compHom M (algebraMap (CompletedTower A t p) S)
    Module.Finite (CompletedTower A t p) M := by
  let : IsNoetherianRing D := IsNoetherianRing.of_finite A D
  let := flat_completedTower_over_base A t p
  let : Algebra D ((CompletedTower A t p) ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact pushout_koszulModuleHomology_finite A (CompletedTower A t p) D
    ((CompletedTower A t p) ⊗[A] D) z q

/-- 台の条件を満たす列について、比較元の全次数の正規化 Koszul 長さは有限。 -/
theorem completedTensor_koszul_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A) {r : ℕ} (z : Fin r → D)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range (Algebra.TensorProduct.includeRight.toRingHom ∘ z))).radical)
    (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ := by
  exact completedTensorLength_ne_top_of_finite A D t p ht hp _
    (completedTensor_koszulModuleHomology_finite A D t p z q)
    (isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
      (Algebra.TensorProduct.includeRight.toRingHom ∘ z) hJ
      (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D)) q)

omit [IsLocalRing A] in
/-- 任意の有限段から来る列でも、比較元のホモロジーは完備塔上有限生成。 -/
theorem completedTensor_stage_koszulModuleHomology_finite
    (n : ℕ) {r : ℕ} (z : Fin r → Section2.StageAlgebra A D t p n) (q : ℤ) :
    let S := (CompletedTower A t p) ⊗[A] D
    let M := (((koszulModuleFunctor
      ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj (ModuleCat.of S S)).homology q)
    let _ := Module.compHom M (algebraMap (CompletedTower A t p) S)
    Module.Finite (CompletedTower A t p) M := by
  let := Section2.completedTensorStageAlgebra A D t p n
  let := Section2.completedTensorStageScalarTower A D t p n
  let := Section2.completedTensorStageIsPushout A D t p n
  let := flat_completedTower_over_stage A t p n
  let : Module.Finite (TowerStage A t p n) (Section2.StageAlgebra A D t p n) :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact pushout_koszulModuleHomology_finite (TowerStage A t p n)
    (CompletedTower A t p) (Section2.StageAlgebra A D t p n)
    ((CompletedTower A t p) ⊗[A] D) z q

/-- 有限段の列の台の条件から、完備テンソル代数の全 Koszul 長さの有限性を導く。 -/
theorem completedTensor_stage_koszul_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A) (n : ℕ) {r : ℕ}
    (z : Fin r → Section2.StageAlgebra A D t p n)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical)
    (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ := by
  exact completedTensorLength_ne_top_of_finite A D t p ht hp _
    (completedTensor_stage_koszulModuleHomology_finite A D t p n z q)
    (isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
      ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z) hJ
      (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D)) q)

/-- 有限段のパラメータ系では台の条件も自動的に満たす。 -/
theorem completedTensor_stage_parameter_source_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A) (n : ℕ) [IsLocalRing (Section2.StageAlgebra A D t p n)]
    (hinj : Function.Injective (algebraMap A (Section2.StageAlgebra A D t p n)))
    {r : ℕ} (z : Fin r → Section2.StageAlgebra A D t p n)
    (hz : IsSystemOfParameters (Section2.StageAlgebra A D t p n) z) (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ :=
  completedTensor_stage_koszul_length_ne_top A D t p ht hp n z
    (completedTensorMaxIdeal_le_stage_parameter_radical A D t p n hinj z hz) q

/-- D のパラメータ系では、台と有限生成性をともに構成から供給できる。 -/
theorem completedTensor_parameter_source_length_ne_top
    [IsLocalRing D] (hp : (p : A) ∈ maximalIdeal A)
    (hinj : Function.Injective (algebraMap A D))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ :=
  completedTensor_koszul_length_ne_top A D t p ht hp z
    (completedTensorMaxIdeal_le_parameter_radical A D t p hinj z hz) q

end SerrePositivity.CLMST

end CompletedSourceLengthPart

section CompletedCokernelFiniteEulerPart

open scoped _root_.TensorProduct
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory
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

end CompletedCokernelFiniteEulerPart

section SourceEulerEvaluationPart

open scoped _root_.TensorProduct _root_.ENNReal
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (hp : (p : A) ∈ maximalIdeal A)
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))

include ht hp htD hres in
/-- 各次数の比較元の正規化長さは、有限段の通常長さを段の階数で割った値。 -/
theorem completedTensor_stage_source_homology_length
    (n : ℕ) {r : ℕ} (y : Fin r → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing A D t p htD n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) =
    (Module.length (Section2.StageAlgebra A D t p n) ((koszulComplex y).homology q) : ℝ≥0∞) /
      (stageRank h p n : ℝ≥0∞) := by
  let := Section2.stageAlgebra_isLocalRing A D t p htD n
  let := Section2.completedTensorStageAlgebra A D t p n
  let := Section2.completedTensorStageScalarTower A D t p n
  let := Section2.completedTensorStageIsPushout A D t p n
  let := flat_completedTower_over_stage A t p n
  rw [koszulModuleFunctor_self_eq]
  let H := (koszulComplex y).homology q
  let N := (koszulComplex ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).homology q
  let : Module (TowerStage A t p n) H := Module.compHom H
    (algebraMap (TowerStage A t p n) (Section2.StageAlgebra A D t p n))
  let : Module (CompletedTower A t p) N := Module.compHom N
    (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D))
  have hlength : Module.length (TowerStage A t p n) H =
      Module.length (Section2.StageAlgebra A D t p n) H :=
    Section2.length_restrictScalars_stageAlgebra_eq A D t p htD hres n H
  have hfinite : IsFiniteLength (TowerStage A t p n) H := by
    apply Module.length_ne_top_iff.mp
    rw [hlength]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_koszulHomology_of_isSystemOfParameters _ y hy q)
  let e : N ≃ₗ[CompletedTower A t p]
      (CompletedTower A t p ⊗[TowerStage A t p n] H) :=
    pushoutKoszulHomologyEquiv (TowerStage A t p n) (CompletedTower A t p)
    (Section2.StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) y q
  change (RootTowerLength.completedNormalizedLength A t p ht).len N = _
  rw [(RootTowerLength.completedNormalizedLength A t p ht).len_congr _ _ e]
  rw [RootTowerLength.completedNormalizedLength_tensor_eq_length A t p ht hp n H hfinite]
  rw [hlength]

include ht hp htD hres in
/-- 比較元の Euler 評価は有限段の通常の Koszul Euler 数を正規化した値。 -/
theorem completedTensor_stage_source_euler_eq_chiOrd
    (n : ℕ) {r : ℕ} (y : Fin r → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing A D t p htD n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
      chiOrd (koszulComplex y) / (stageRank h p n : ℝ) := by
  unfold lambdaEuler chiOrd
  simp only [completedTensor_stage_source_homology_length A D t p ht hp htD hres n y hy,
    ENNReal.toReal_div, ENNReal.toReal_natCast, toReal_toENNReal]
  simp only [div_eq_mul_inv, ← mul_assoc, finsum_mul]

include ht hp htD hres in
/-- 証明済みの Koszul 重複度公式により、比較元の Euler 評価は有限段の重複度の正規化。 -/
theorem completedTensor_stage_source_euler_eq_multiplicity
    (n : ℕ) {r : ℕ} (y : Fin r → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing A D t p htD n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
      (HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n)
        (Ideal.span (Set.range y)) (Section2.StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ) := by
  let := Section2.stageAlgebra_isLocalRing A D t p htD n
  rw [completedTensor_stage_source_euler_eq_chiOrd A D t p ht hp htD hres n y hy,
    KoszulMultiplicity.multiplicity_eq_chiOrd_koszul y hy]

end SerrePositivity.CLMST

end SourceEulerEvaluationPart

section CompletedTargetLengthPart

open scoped _root_.TensorProduct
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory
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
    (n : ℕ) (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y)
    (q : ℤ) (hq : q < 0) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) = 0 := by
  let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
    Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  let S := (CompletedTower A t p) ⊗[A] D
  let C := RPerfd A D t p hperf
  let z := (Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y
  let i : ℕ := (-q).toNat
  have hi : 0 < i := by dsimp [i]; omega
  have hqi : q = -(i : ℤ) := by dsimp [i]; omega
  have hseq : algebraMap S C ∘ z = fun j ↦ toRPerfd A D t p hperf n (y j) := by
    funext j
    change toMixedPerfectoid A D t p hperf (Section2.stageToCompletedTensor A D t p n (y j)) = _
    exact stageToCompletedTensor_toMixedPerfectoid A D t p hperf n (y j)
  have hann :
      let _ := Module.compHom ((koszulComplex (algebraMap S C ∘ z)).homology q)
        (algebraMap (CompletedTower A t p) C)
      Almost.IsAlmostZero
        (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g))
        ((koszulComplex (algebraMap S C ∘ z)).homology q) := by
    rw [hseq, hqi]
    exact (corollary_4_0_4 A D hinj hres t hdimA hdimD hpos ht hsop
      p htp e he hperf g hg hEtale).2 n y hy i hi
  let H := (koszulComplex (algebraMap S C ∘ z)).homology q
  let := Module.compHom H (algebraMap (CompletedTower A t p) C)
  have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
    (by
      rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
      exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj) y hy
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
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y)
    (b : CompletedTower A t p) (N : ℕ)
    (hN : ∀ x : (RPerfd A D t p hperf) ⧸
      (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
        ((CompletedTower A t p) ⊗[A] D) p hperf).range, b ^ N • x = 0)
    (hyLast : Section2.stageToCompletedTensor A D t p n (y (Fin.last r)) ∈
      Ideal.span (Set.range (Fin.init ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y))) ⊔
        Ideal.span {(algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) b) ^ N}) :
    let lam := completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
    let z := (Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y
    let S := (CompletedTower A t p) ⊗[A] D
    let C := RPerfd A D t p hperf
    (lambdaEuler lam ((koszulModuleFunctor z).obj
      (ModuleCat.of S (AlgebraMapCokernel S C))) = 0) ∧
    (lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
      lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S))) := by
  subst h
  let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
    Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp, ← ht]
    exact Ideal.subset_span (Set.mem_range_self _)
  have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
    (by
      rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
      exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj) y hy
  have hinjC := toMixedPerfectoid_injective_of_domain A D t p hperf hinj g hg hEtale
  have hC : ∀ q : ℤ, q < 0 →
      (completedTensorLength A D t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
        (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
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

end CompletedTargetLengthPart

section SelectedParameterEulerPart

open scoped _root_.TensorProduct
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory
attribute [local instance] HasDerivedCategory.standard

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

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 任意の有限段のパラメータ系に対し、実際の零化冪と所属を満たす列を選び Euler 比較を適用する。 -/
theorem exists_selected_parameter_euler_comparison
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    ∃ (y' : Fin (r + 1) → Section2.StageAlgebra A D t p n) (k : ℕ),
      Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
      IsSystemOfParameters (Section2.StageAlgebra A D t p n)
        (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
      (let lam := completedTensorLength A D t p
         (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
       let z := (Section2.stageToCompletedTensor A D t p n).toRingHom ∘
         Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
       let S := (CompletedTower A t p) ⊗[A] D
       let C := RPerfd A D t p hperf
       (lambdaEuler lam ((koszulModuleFunctor z).obj
         (ModuleCat.of S (AlgebraMapCokernel S C))) = 0) ∧
       (lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S C)) =
         lambdaEuler lam ((koszulModuleFunctor z).obj (ModuleCat.of S S))) ∧
       (∀ q : ℤ, lam.len (((koszulModuleFunctor z).obj
         (ModuleCat.of S C)).homology q) ≠ ⊤)) := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
    Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  dsimp only
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp, ← ht]
    exact Ideal.subset_span (Set.mem_range_self _)
  obtain ⟨g, N, hg, _, hgmD, hNpos, hEtale, _, hN⟩ :=
    exists_nonunit_completedTensor_positive_isogeny A D t p hperf hinj hp
  have htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D := by
    intro i
    rw [← hsop.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  have hgD : algebraMap A D g ≠ 0 := fun hzero ↦ hg (hinj (hzero.trans (map_zero _).symm))
  have hgreg : IsSMulRegular D (algebraMap A D g) := fun x y hxy ↦
    mul_left_cancel₀ hgD hxy
  obtain ⟨y', k, hspan, hk, hparam, hmem⟩ :=
    Section2.stage_parameter_power_selection_completed_of_regular_base A D t p htD n
      g hgmD hgreg N hNpos y hy
  let w := Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
  have hprefix : Fin.init ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w) =
      Section2.stageToCompletedTensor A D t p n ∘ Fin.init y' := by
    funext i
    simp only [Fin.init, Function.comp_apply, w, Fin.snoc_castSucc]
    rfl
  have hscalar : algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
      (algebraMap A (CompletedTower A t p) g) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) g :=
    (IsScalarTower.algebraMap_apply A (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) g).symm
  have hLast : Section2.stageToCompletedTensor A D t p n (w (Fin.last r)) ∈
      Ideal.span (Set.range (Fin.init ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w))) ⊔
        Ideal.span {(algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
          (algebraMap A (CompletedTower A t p) g)) ^ N} := by
    rw [hprefix, hscalar]
    exact hmem
  have hcompare := completedTensor_stage_parameter_euler_comparison A D hinj hres
    t hdimA hdimD hpos ht hsop p htp e he hperf g hg hEtale n hr w hparam
    (algebraMap A (CompletedTower A t p) g) N hN hLast
  refine ⟨y', k, hspan, hk, hparam, ?_⟩
  refine ⟨hcompare.1, hcompare.2, ?_⟩
  let : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D
  let R := CompletedTower A t p
  let S := R ⊗[A] D
  let z := (Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w
  let lam := completedTensorLength A D t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
  have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
    (by
      rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
      exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj) w hparam
  have hinjC := toMixedPerfectoid_injective_of_domain A D t p hperf hinj g hg hEtale
  have hC : ∀ q : ℤ, q < 0 → lam.len
      (((koszulModuleFunctor z).obj (ModuleCat.of S (RPerfd A D t p hperf))).homology q) ≠ ⊤ := by
    intro q hq
    have hyh : IsSystemOfParameters (Section2.StageAlgebra A D t p n)
        (fun j : Fin h ↦ w (Fin.cast hr j)) := by
      subst h
      simpa using hparam
    have hzero := completedTensor_stage_target_koszul_length_eq_zero A D hinj hres
      t hdimA hdimD hpos ht hsop p htp e he hperf g hg hEtale n
      (fun j : Fin h ↦ w (Fin.cast hr j)) hyh q hq
    subst h
    change lam.len (((koszulModuleFunctor z).obj
      (ModuleCat.of S (RPerfd A D t p hperf))).homology q) = 0 at hzero
    rw [hzero]
    exact ENNReal.zero_ne_top
  have lNegative := completedTensor_stage_cokernel_negative_length_ne_top A D t p _ hperf
    hp hinjC n w hJ hC
  exact lambdaKoszul_algebraMap_target_ne_top_of_last_mem_span_sup lam
    (RPerfd A D t p hperf) hinjC (completedTensorMaxIdeal_fg A D t p) z hJ
    ((algebraMap R S (algebraMap A R g)) ^ N)
    (perfectoidizationCokernel_annihilated R S p hperf (algebraMap A R g) N hN) hLast
    (completedTensor_stage_koszul_length_ne_top A D t p _ hp n w hJ) lNegative

end SerrePositivity.CLMST

end SelectedParameterEulerPart

section CompletedParameterFinitenessPart

open scoped _root_.TensorProduct
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.CategoryTheory

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

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 選択した正冪の列の零次の有限性を、元の任意のパラメータ系へ戻す。 -/
theorem completedTensor_stage_parameter_zero_length_ne_top
    (n : ℕ) (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology 0) ≠ ⊤ := by
  cases h with
  | zero => omega
  | succ r =>
    let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
      Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    obtain ⟨y', k, hspan, hk, hparams, _, _, hfinite⟩ :=
      exists_selected_parameter_euler_comparison A D hinj hres t hdimA hdimD hpos
        ht hsop p htp e he hperf n rfl y hy
    let w := Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
    have hwJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
      (by
        rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
        exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj) w hparams
    have hle : Ideal.span (Set.range w) ≤ Ideal.span (Set.range y) :=
      (span_last_pow_le y' k hk).trans_eq hspan
    have hSm : Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w)) ≤
        Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)) := by
      have hm := Ideal.map_mono (f := (Section2.stageToCompletedTensor A D t p n).toRingHom) hle
      simpa only [Ideal.map_span, ← Set.range_comp] using hm
    exact ne_top_of_le_ne_top (hfinite 0)
      (LengthAlgebra.lambdaKoszul_homology_zero_le_of_span_le
        (completedTensorLength A D t p _) (RPerfd A D t p hperf)
        (completedTensorMaxIdeal_fg A D t p)
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w)
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y) hwJ hSm)

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 全有限段の任意のパラメータ系について、零次数を含む全 Koszul 長さが有限。 -/
theorem completedTensor_stage_parameter_length_ne_top
    (n : ℕ) (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) (q : ℤ) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) ≠ ⊤ := by
  by_cases hq : q = 0
  · subst q
    exact completedTensor_stage_parameter_zero_length_ne_top A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf n y hy
  by_cases hneg : q < 0
  · obtain ⟨g, hg, hEtale⟩ := exists_finite_etale_away A D hinj
    rw [completedTensor_stage_target_koszul_length_eq_zero A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf g hg hEtale.2 n y hy q hneg]
    exact ENNReal.zero_ne_top
  · let := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ q
      (koszulModuleFunctor_isZero_X_of_pos
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf)) q (by omega)))
    rw [NormalizedLength.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top

end SerrePositivity.CLMST

end CompletedParameterFinitenessPart
