module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GenericPrimeBaseChange
public import SerrePositivity.AlgebraicGeometry.PureFreeStalkBaseChange

/-!
概要：KST §5、Stacks 0810・0811 の一般点で自由な純変換の追加基底変更。
方針：旧一般点局所環から新局所環への写像に、有限加群の平坦な純変換の基底変更同型を適用する。
規約：追加係数環で境界元は正則とし、元の加群の全体での相対平坦性は要求しない。
使われ方：一般点自由化をさらに細分する admissible blowup で保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：全拡大一般点で同じ階数の自由な純変換は、正則な境界を保つ任意の基底変更後も同じ階数で自由。
方針：拡大素点の縮約を照合し、局所化比較・平坦な純変換の基底変更同型・テンソル取消を合成する。
規約：KST §5、Stacks 0810・0811、実分裂と Noether 係数環を入力する。
使われ方：自由化中心を共通細分で置き換える際の一般点自由性の保存。
-/
theorem genericPureTransformFree_baseChange
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (r : ℕ)
    (hfree : ∀ P : PrimeSpectrum A,
      let Q := geometricallyIntegralGenericPrime A B P
      Q ∈ Module.freeLocus B (modulePureTransform (algebraMap A B f) M) ∧
        Module.rankAtStalk (modulePureTransform (algebraMap A B f) M) Q = r)
    (hf : IsRegular (algebraMap A C f)) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    ∀ P : PrimeSpectrum C,
      let Q := geometricallyIntegralGenericPrime C D P
      let G := modulePureTransform (algebraMap C D (algebraMap A C f)) (D ⊗[B] M)
      Q ∈ Module.freeLocus D G ∧ Module.rankAtStalk G Q = r := by
  dsimp only
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  intro P
  let Q := geometricallyIntegralGenericPrime C D P
  let q := Q.comap (algebraMap B D)
  let L := Localization.AtPrime Q.asIdeal
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hq : q = geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P) :=
    geometricallyIntegralGenericPrime_baseChange_comap A B C e p hpe P
  let G := modulePureTransform (algebraMap A B f) M
  have hqfree : q ∈ Module.freeLocus B G := by rw [hq]; exact (hfree _).1
  have hqrank : Module.rankAtStalk G q = r := by rw [hq]; exact (hfree _).2
  let d := algebraMap D L (algebraMap C D (algebraMap A C f))
  have hd : IsRegular d := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (S := L) Q.asIdeal.primeCompl
      (isRegular_iff_mem_nonZeroDivisors.mp
        (algebraMap_isRegular_of_flat C D (algebraMap A C f) hf))
  have hscalar : algebraMap B D (algebraMap A B f) =
      algebraMap C D (algebraMap A C f) := by
    rw [← IsScalarTower.algebraMap_apply A B D, IsScalarTower.algebraMap_apply A C D]
  have hd' : IsRegular (algebraMap D L (algebraMap B D (algebraMap A B f))) := by
    rwa [hscalar]
  have h := pureTransform_freeLocus_rankAtStalk_baseChange
    (M := M) (algebraMap A B f) r Q ⟨hqfree, hqrank⟩ hd'
  rwa [hscalar] at h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
