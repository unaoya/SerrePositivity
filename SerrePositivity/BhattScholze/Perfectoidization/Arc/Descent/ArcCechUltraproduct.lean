module

public import SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
## 概要
超積の族による増大 Čech 完全性の検出（BM18 Lemma 3.25）。
## 方針
平坦局所化とホモロジーを交換し、元の零化イデアルを含む素点で検出する。
## 規約
可換環の任意の積を基底とする。
## 使われ方
絶対整閉付値環の積の上で構造層の Čech 完全性を検査する。
-/

@[expose] public noncomputable section

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.TensorProduct

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

variable {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)]

/-- 超フィルターによる局所化の族は加群の零性を検出する
（BM18 Lemma 3.25 の構造層の場合）。 -/
theorem subsingleton_of_ultraproduct_tensor (M : Type u) [AddCommGroup M] [Module (∀ i, R i) M]
    (h : ∀ U : Ultrafilter ι, Subsingleton (RingUltraproduct R U ⊗[∀ i, R i] M)) :
    Subsingleton M := by
  let A := ∀ i, R i
  refine ⟨fun x y => sub_eq_zero.mp ?_⟩
  let m := x - y
  change m = 0
  by_contra hm
  let I : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A M m)
  have hI : I ≠ ⊤ := by
    intro he
    apply hm
    have h1 : (1 : A) ∈ I := by rw [he]; trivial
    change (1 : A) • m = 0 at h1
    rwa [one_smul] at h1
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  let q : PrimeSpectrum A := ⟨P, hP.isPrime⟩
  let U := ultrafilterOfPrime R q
  let B := RingUltraproduct R U
  let S := ultrafilterDenominators R U
  let : IsLocalization S B := isLocalization_ringUltraproduct R U
  let f := TensorProduct.mk A B M 1
  have hf : f m = f 0 := (h U).elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hf
  have hsI : (s : A) ∈ I := by
    change (s : A) • m = 0
    exact hs.trans (smul_zero _)
  exact ultrafilterDenominators_le_primeCompl R q s.property (hIP hsI)

open BhattScholze.Perfectoidization.Derived in
/-- 超積への底変換の族は増大 Čech 完全性を検出する（BM18 Lemma 3.25）。 -/
theorem cechExact_of_ultraproducts
    (B : Under (CommRingCat.of (∀ i, R i)))
    (h : ∀ U : Ultrafilter ι, Cech.IsCechExact
      (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of (∀ i, R i))
        (CommRingCat.of (RingUltraproduct R U))).obj B).hom)) :
    Cech.IsCechExact (Arrow.mk B.hom) := by
  apply (Cech.moduleCech_acyclic_iff B).mp
  intro n
  let K := Cech.moduleCech B
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_ultraproduct_tensor R
  intro U
  let A := ∀ i, R i
  let D := RingUltraproduct R U
  let : IsLocalization (ultrafilterDenominators R U) D := isLocalization_ringUltraproduct R U
  let : Module.Flat A D := IsLocalization.flat D (ultrafilterDenominators R U)
  let F := tensorLeft (ModuleCat.of A D)
  let e := (K.sc n).mapHomologyIso F
  have hK := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_baseChange_iff_tensorCochain B D).mp (h U) n
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hK
  exact ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso e.symm)

end SerrePositivity
