module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Flat.Basic

/-!
概要：KST §5、Stacks 05C2・05E0 のファイバーの随伴素イデアルの縮約。
方針：剰余体で零となる元と非零となる元のスカラー作用を、平坦テンソルへ移す。
規約：剰余体を右因子とし、左因子の環上の随伴素イデアルを使う。
使われ方：素イデアル剰余から剰余体への単射による包含を元のファイバー条件へ接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：剰余体の右テンソルでは、元の環の素イデアルに属する元は全体を零化する。
方針：純テンソルでスカラーを剰余体側へ移し、剰余体写像の核を使う。
規約：KST §5、Stacks 05E0、平坦性は零作用には不要。
使われ方：ファイバーの随伴素イデアルの縮約への素イデアルの包含。
-/
theorem smul_tensor_residueField_eq_zero
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    (p : Ideal R) [p.IsPrime] (r : R) (hr : r ∈ p) (x : N ⊗[R] p.ResidueField) :
    r • x = 0 := by
  have hr0 : algebraMap R p.ResidueField r = 0 := by
    change r ∈ RingHom.ker (algebraMap R p.ResidueField)
    rwa [Ideal.ker_algebraMap_residueField]
  induction x using TensorProduct.inductionOn with
  | tmul n a =>
      rw [← TensorProduct.tmul_smul]
      simp [Algebra.smul_def, hr0]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/--
概要：平坦加群と剰余体のテンソルでは、素イデアルの外の元の作用は単射。
方針：剰余体での非零スカラー乗法の単射性を平坦テンソルへ移す。
規約：KST §5、Stacks 05C2・05E0、テンソルのスカラー作用は元の環上のもの。
使われ方：ファイバーの随伴素イデアルの縮約から外の元を除く。
-/
theorem smul_tensor_residueField_injective
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (r : R) (hr : r ∉ p) :
    Function.Injective (fun x : N ⊗[R] p.ResidueField => r • x) := by
  have hr0 : algebraMap R p.ResidueField r ≠ 0 := by
    intro h
    apply hr
    change r ∈ RingHom.ker (algebraMap R p.ResidueField) at h
    rwa [Ideal.ker_algebraMap_residueField] at h
  have hinj : Function.Injective (DistribSMul.toLinearMap R p.ResidueField r) := by
    intro a b hab
    change r • a = r • b at hab
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hr0 hab
  have ht := Module.Flat.lTensor_preserves_injective_linearMap (M := N)
    (DistribSMul.toLinearMap R p.ResidueField r) hinj
  rw [LinearMap.lTensor_smul_action] at ht
  exact ht

/--
概要：平坦加群の剰余体ファイバーの随伴素イデアルは、元の基礎環へ元の素イデアルに縮約する。
方針：非零元の零化イデアルという表示を選び、素イデアルの内外の作用の零性・単射性を使う。
規約：KST §5、Stacks 05C2・05E0、随伴素イデアルを取る環 S は Noether とする。
使われ方：ファイバーの随伴素イデアルの条件による完備化への普遍単射性。
-/
theorem associatedPrime_tensor_residueField_comap
    {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S)
    (hq : q ∈ associatedPrimes S (N ⊗[R] p.ResidueField)) :
    q.comap (algebraMap R S) = p := by
  obtain ⟨hqprime, x, hx⟩ := isAssociatedPrime_iff.mp hq
  have hx0 : x ≠ 0 := by
    intro h
    apply hqprime.ne_top
    rw [hx, h]
    simp
  ext r
  constructor
  · intro hr
    by_contra hrp
    have hrx : algebraMap R S r • x = 0 := by
      change algebraMap R S r ∈ q at hr
      rw [hx, Submodule.mem_colon_singleton] at hr
      exact hr
    have hrx' : r • x = 0 := by simpa only [algebraMap_smul] using hrx
    exact hx0 (smul_tensor_residueField_injective (N := N) p r hrp (by simpa using hrx'))
  · intro hr
    change algebraMap R S r ∈ q
    rw [hx, Submodule.mem_colon_singleton]
    change algebraMap R S r • x = 0
    simpa only [algebraMap_smul] using smul_tensor_residueField_eq_zero p r hr x

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
