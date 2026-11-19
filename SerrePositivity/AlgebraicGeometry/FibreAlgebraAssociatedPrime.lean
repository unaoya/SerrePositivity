module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralFiberRegularity
public import SerrePositivity.AlgebraicGeometry.TensorFibreAssociatedPrimes
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
概要：KST §5、Stacks 05FS の幾何学的整なファイバーの随伴素イデアル。
方針：整域代数の非零元の零化イデアルは構造写像の核であり、平坦性でファイバー写像の核を計算する。
規約：ファイバーは B⊗κ(p) とし、B 加群としての随伴素イデアルを使う。
使われ方：完備基底上での 05DP のファイバー条件の自動的な成立。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：整域代数を元の環の加群とした随伴素イデアルは、構造写像の核に一致する。
方針：非零元の零化イデアルを整域で計算する。
規約：KST §5、Stacks 05FS、随伴素イデアルを取る環は Noether。
使われ方：幾何学的整なファイバーの唯一の随伴素イデアルを計算する。
-/
theorem associatedPrime_algebra_of_domain_eq_ker
    {B C : Type u} [CommRing B] [IsNoetherianRing B]
    [CommRing C] [IsDomain C] [Algebra B C] (q : Ideal B)
    (hq : q ∈ associatedPrimes B C) : q = RingHom.ker (algebraMap B C) := by
  obtain ⟨hqprime, x, hx⟩ := isAssociatedPrime_iff.mp hq
  have hx0 : x ≠ 0 := by
    intro h
    apply hqprime.ne_top
    rw [hx, h]
    simp
  ext b
  rw [hx, Submodule.mem_colon_singleton]
  change b • x = 0 ↔ algebraMap B C b = 0
  simp only [Algebra.smul_def, mul_eq_zero, hx0, or_false]

/--
概要：平坦代数から剰余体ファイバーへの構造写像の核は、元の素イデアルの拡大。
方針：素イデアル剰余と剰余体の間の単射をテンソルし、拡大イデアルによる商の同型を使う。
規約：KST §5、Stacks 05FS、Noether 性や幾何学的整性は核の計算には不要。
使われ方：ファイバーの随伴素イデアルを拡大素イデアルと同定する。
-/
theorem ker_algebraMap_tensor_residueField
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] :
    RingHom.ker (algebraMap B (B ⊗[A] p.ResidueField)) = p.map (algebraMap A B) := by
  let j : (A ⧸ p) →ₗ[A] p.ResidueField :=
    (IsScalarTower.toAlgHom A (A ⧸ p) p.ResidueField).toLinearMap
  let J := TensorProduct.AlgebraTensorModule.lTensor B B j
  have hJ : Function.Injective J :=
    Module.Flat.lTensor_preserves_injective_linearMap j
      p.injective_algebraMap_quotient_residueField
  let E := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p
  have hcomp (b : B) : J (E (Ideal.Quotient.mk _ b)) =
      algebraMap B (B ⊗[A] p.ResidueField) b := by
    simp [J, j, E, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  ext b
  change algebraMap B (B ⊗[A] p.ResidueField) b = 0 ↔ _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hb
    have hE : E (Ideal.Quotient.mk _ b) = 0 := hJ (by rw [hcomp, map_zero]; exact hb)
    exact E.injective (by simpa only [map_zero] using hE)
  · intro hb
    rw [← hcomp, hb, map_zero, map_zero]

/--
概要：幾何学的整な平坦代数の剰余体ファイバーの随伴素イデアルは、元の素イデアルの拡大。
方針：幾何学的整性によるファイバー環の整域性と構造写像の核の計算を合わせる。
規約：KST §5、Stacks 05FS、B は Noether とし有限性は別の仮定から用意できる。
使われ方：完備基底での射影性判定のファイバー条件。
-/
theorem associatedPrime_tensor_residueField_eq_extendedPrime
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Module.Flat A B]
    [_root_.AlgebraicGeometry.GeometricallyIntegral
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (p : Ideal A) [p.IsPrime] (q : Ideal B)
    (hq : q ∈ associatedPrimes B (B ⊗[A] p.ResidueField)) :
    q = p.map (algebraMap A B) := by
  let := isDomain_tensor_of_geometricallyIntegral A B p.ResidueField
  let : IsDomain (B ⊗[A] p.ResidueField) :=
    (Algebra.TensorProduct.comm A B p.ResidueField).toRingEquiv.toMulEquiv.isDomain _
  exact (associatedPrime_algebra_of_domain_eq_ker q hq).trans
    (ker_algebraMap_tensor_residueField p)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
