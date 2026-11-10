module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower

/-!
# 平坦複体の完備な主元簡約による離散性

## 概要
有界な主元ねじれを持つ環上で、主元の冪で零化される係数とのテンソルが離散なら、
その主元に関して導来完備な平坦複体も離散。

## 方針
実余核の塔の各段と遷移を調べ、Milnor 列を適用する。

## 規約
BS 著者版 Lemma 3.7 (2) の鎖複体による議論。複体に次数の上界を仮定しない。

## 使われ方
導来対象の有界性を、完全平坦性と導来完備性から得る。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.DerivedCompletion

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- 概要：主元冪ねじれの係数による純性は、完備な平坦複体の純性を与える。
方針：余核の塔に対する再構成と零次遷移の全射性を使う。
規約：導来完備性と環の有界ねじれ。複体は任意の整数次数。
使われ方：BS 著者版 Lemma 3.7 (2) の離散性。 -/
theorem isZero_homology_of_complete_of_powerTorsion_tests (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (hc : IsComplete R a (DerivedCategory.Q.obj K))
    (N : ℕ) (hN : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (ht : ∀ (n : ℕ) (M : ModuleCat.{u} R), (∀ x : M, a ^ n • x = 0) →
      ∀ i : ℤ, i ≠ 0 → IsZero (((moduleTensorCochainFunctor K).obj M).homology i))
    (i : ℤ) (hi : i ≠ 0) : IsZero (K.homology i) := by
  let F := moduleTensorCochainFunctor K
  let L := powerCokernelComplex a K
  let t := powerCokernelComplexTransition a K
  let e := powerCokernelTensorModelIso a K hK
  have hann (n : ℕ) (x : R ⧸ Ideal.span {a ^ n}) :
      a ^ n • x = 0 := by
    change Ideal.Quotient.mk (Ideal.span {a ^ n}) (a ^ n) * x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_mul]
  have hz (n : ℕ) (j : ℤ) (hj : j ≠ 0) : IsZero ((L n).homology j) := by
    exact (ht n (ModuleCat.of R (R ⧸ Ideal.span {a ^ n})) (hann _) j hj).of_iso
      ((homologyFunctor (ModuleCat R) (.up ℤ) j).mapIso (e n))
  have hsurj (n : ℕ) : Function.Surjective (homologyMap (t n) 0) := by
    let f := powerQuotientCoefficientTransition a n
    let S : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk (kernel.ι f) f (kernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_kernel _, mono_f := inferInstance, epi_g := inferInstance }
    have hk (x : (kernel f : ModuleCat.{u} R)) : a ^ (n + 1) • x = 0 := by
      apply (ModuleCat.mono_iff_injective (kernel.ι f)).mp inferInstance
      simpa only [map_smul, map_zero] using hann (n + 1) (kernel.ι f x)
    have hkz := ht (n + 1) (kernel f) hk 1 (by omega)
    have he := (moduleTensorCochain_shortExact K hK S hS).homology_exact₃ 0 1 rfl
    let H := homologyFunctor (ModuleCat R) (.up ℤ) 0
    let : Epi (H.map (F.map f)) := he.epi_f (hkz.eq_of_tgt _ _)
    have hw := congrArg H.map (powerCokernelTensorModelIso_transition a K hK n)
    simp only [Functor.map_comp] at hw
    have hep : Epi (H.map (t n) ≫ H.map (e n).hom) := by
      rw [hw]
      infer_instance
    have := (epi_comp_iff_of_isIso (H.map (t n)) (H.map (e n).hom)).mp hep
    exact (ModuleCat.epi_iff_surjective _).mp this
  have hdiff (j : ℤ) : Function.Surjective (complexTowerHomologyDifference R L t j) := by
    apply moduleTowerDifference_surjective
    intro n
    by_cases hj : j = 0
    · subst j
      exact hsurj n
    · have hn : IsZero ((L n).homology j) := hz n j hj
      exact fun y ↦ ⟨0, (ModuleCat.isZero_iff_subsingleton.mp hn).elim _ _⟩
  have hm := complexTowerMilnorProjection_injective_of_surjective R L t i (hdiff (i - 1))
  have htower : IsZero ((complexTowerHomotopyLimit R L t).homology i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y ↦ hm ?_⟩
    apply Subtype.ext
    funext n
    have hn : IsZero ((L n).homology i) := hz n i hi
    exact (ModuleCat.isZero_iff_subsingleton.mp hn).elim _ _
  let := powerCokernelReconstruction_quasiIso a K hK N hN hc
  exact htower.of_iso (asIso (homologyMap (powerCokernelReconstruction a K) i))

end SerrePositivity.DerivedCompletion
