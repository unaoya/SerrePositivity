module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformStalkEquiv
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import SerrePositivity.AlgebraicGeometry.FlatPureTransformBaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
概要：KST §5、Stacks 0810・0811 の一つの素点で自由な純変換の任意の基底変更。
方針：縮約素点の局所環から新局所環への写像に平坦な純変換の基底変更同型を適用する。
規約：Noether 条件と加群の有限性は元の環に課す。
使われ方：テンソル積の特定の表示に依存せず、自由な純変換の追加基底変更を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：正則元の平坦代数への像は正則。
方針：平坦加群上の正則スカラー作用を代数内の乗法の単射性へ書き換える。
規約：KST §5、Stacks 0810・0811、忠実平坦性や Noether 性は不要。
使われ方：追加基底変更した代数の一般点局所環で境界が正則であることを確認する。
-/
theorem algebraMap_isRegular_of_flat
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (f : R) (hf : IsRegular f) : IsRegular (algebraMap R S f) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply Module.Flat.isSMulRegular_of_isRegular (M := S) hf
  simpa only [Algebra.smul_def, mul_zero] using hx

set_option backward.isDefEq.respectTransparency false in
/--
概要：縮約素点で自由な純変換は、新局所環で境界が正則なら基底変更後にも自由で同じ局所階数。
方針：純変換の局所化比較と、旧局所環から新局所環への平坦な純変換の基底変更同型を合成する。
規約：KST §5、Stacks 0810・0811、幾何学的整性や係数環の平坦性は不要。
使われ方：一般点の縮約と境界の正則性を照合した後の局所自由性の保存。
-/
theorem pureTransform_freeLocus_rankAtStalk_baseChange
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : R) (r : ℕ) (Q : PrimeSpectrum S)
    (hfree : Q.comap (algebraMap R S) ∈ Module.freeLocus R (modulePureTransform f M) ∧
      Module.rankAtStalk (modulePureTransform f M) (Q.comap (algebraMap R S)) = r)
    (hf : IsRegular (algebraMap S (Localization.AtPrime Q.asIdeal) (algebraMap R S f))) :
    Q ∈ Module.freeLocus S (modulePureTransform (algebraMap R S f) (S ⊗[R] M)) ∧
      Module.rankAtStalk (modulePureTransform (algebraMap R S f) (S ⊗[R] M)) Q = r := by
  let P := Q.comap (algebraMap R S)
  let L₀ := Localization.AtPrime P.asIdeal
  let L := Localization.AtPrime Q.asIdeal
  let := Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  let N₀ := L₀ ⊗[R] M
  let d₀ := algebraMap R L₀ f
  let dS := algebraMap R S f
  let d := algebraMap S L dS
  let G := modulePureTransform f M
  let : Module.Free L₀ (LocalizedModule P.asIdeal.primeCompl G) :=
    Module.mem_freeLocus.mp hfree.1
  let E₀ := pureTransformAtPrimeTensorEquiv (M := M) P.asIdeal f
  let : Module.Free L₀ (modulePureTransform d₀ N₀) := Module.Free.of_equiv E₀
  have hr₀ : Module.finrank L₀ (modulePureTransform d₀ N₀) = r :=
    E₀.finrank_eq.symm.trans hfree.2
  have hscalar : algebraMap L₀ L d₀ = d := by
    rw [← IsScalarTower.algebraMap_apply R L₀ L, IsScalarTower.algebraMap_apply R S L]
  have hd : IsRegular (algebraMap L₀ L d₀) := hscalar.symm ▸ hf
  have E₁ : modulePureTransform d (L ⊗[L₀] N₀) ≃ₗ[L]
      L ⊗[L₀] modulePureTransform d₀ N₀ := by
    rw [← hscalar]
    exact flatPureTransformBaseChangeEquiv L d₀ N₀ hd
  let E₂ : (L ⊗[L₀] N₀) ≃ₗ[L] (L ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R L₀ L L M
  let Eold : modulePureTransform d (L ⊗[R] M) ≃ₗ[L]
      L ⊗[L₀] modulePureTransform d₀ N₀ :=
    (modulePureTransformCongr d E₂).symm.trans E₁
  let Enew : LocalizedModule Q.asIdeal.primeCompl
      (modulePureTransform dS (S ⊗[R] M)) ≃ₗ[L] L ⊗[L₀] modulePureTransform d₀ N₀ :=
    (pureTransformAtPrimeTensorEquiv (M := S ⊗[R] M) Q.asIdeal dS).trans
      ((modulePureTransformCongr d
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S L L M)).trans Eold)
  refine ⟨Module.mem_freeLocus.mpr (Module.Free.of_equiv Enew.symm), ?_⟩
  exact Enew.finrank_eq.trans ((Module.finrank_baseChange).trans hr₀)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
