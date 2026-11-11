module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Ring

/-!
概要：分数体を局所化の前へ移し、体拡大後の整域性を分数体に移す。
方針：分数の分子と分母の共通分母を払い、体拡大後の局所化を比較する。
規約：体への代数構造は指定された塔と両立するものを使う。
使われ方：超曲面模型と元のアフィン族の共通分数体を与える。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：局所化の分数体が局所化前の環を忠実に含むとき、局所化前の環の分数体でもある。
方針：局所化での分数の分子と分母を、元の環の分母を払って書き直す。
規約：局所化に使う乗法部分モノイドは任意。
使われ方：生成ファイバーの関数体を、基底の主開上の模型の関数体として使う。
-/
theorem isFractionRing_of_isFractionRing_localization
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [FaithfulSMul R K] [IsFractionRing S K] (M : Submonoid R) [IsLocalization M S] :
    IsFractionRing R K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, _, hz⟩ := IsFractionRing.div_surjective S z
  obtain ⟨⟨a, m⟩, hx⟩ := IsLocalization.surj M x
  obtain ⟨⟨b, n⟩, hy⟩ := IsLocalization.surj M y
  let f := algebraMap R K
  let g := algebraMap S K
  have unit_map (s : M) : IsUnit (f (s : R)) := by
    change IsUnit (algebraMap R K (s : R))
    rw [IsScalarTower.algebraMap_apply R S K]
    exact (IsLocalization.map_units S s).map g
  have hxK : g x * f (m : R) = f a := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S K, f, g] using congrArg g hx
  have hyK : g y * f (n : R) = f b := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S K, f, g] using congrArg g hy
  refine ⟨a * (n : R), b * (m : R), ?_⟩
  change z = f (a * (n : R)) / f (b * (m : R))
  calc
    z = g x / g y := hz.symm
    _ = g x * (f (m : R) * f (n : R)) / (g y * (f (m : R) * f (n : R))) :=
      (mul_div_mul_right _ _ (mul_ne_zero (unit_map m).ne_zero (unit_map n).ne_zero)).symm
    _ = _ := by
      rw [map_mul, map_mul, ← hxK, ← hyK]
      congr 1 <;> ring

/--
概要：体拡大後に整域となる代数の分数体も、その体拡大後に整域となる。
方針：体拡大後の分数体を、体拡大後の代数の非零元による局所化と比較する。
規約：体拡大で分母の非零性は保たれる。
使われ方：生成ファイバーの関数体に埋め込んだ模型の絶対既約性を得る。
-/
theorem isDomain_tensor_fractionField_of_isDomain_tensor
    {k B L F : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Field L] [Algebra B L] [Algebra k L] [IsScalarTower k B L] [IsFractionRing B L]
    [Field F] [Algebra k F] [IsDomain (F ⊗[k] B)] :
    IsDomain (F ⊗[k] L) := by
  let D := F ⊗[k] B
  let T := F ⊗[k] L
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Module.Free k B := Module.Free.of_divisionRing k B
  have hinj : Function.Injective (algebraMap B D) :=
    Algebra.TensorProduct.includeRight_injective (R := k) (A := F)
      (RingHom.injective (algebraMap k F))
  let : Algebra D T :=
    (Algebra.TensorProduct.map (AlgHom.id k F) (IsScalarTower.toAlgHom k B L)).toAlgebra
  let : IsScalarTower F D T := IsScalarTower.of_algebraMap_eq fun x => by
    change x ⊗ₜ[k] (1 : L) =
      Algebra.TensorProduct.map (AlgHom.id k F) (IsScalarTower.toAlgHom k B L)
        (x ⊗ₜ[k] (1 : B))
    simp
  let : IsLocalization ((B⁰).map (algebraMap B D)) T := by
    change IsLocalization ((B⁰).map (Algebra.TensorProduct.includeRight : B →ₐ[k] D)) T
    exact IsLocalization.tensorProduct_tensorProduct_right k F B⁰ L
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  exact IsLocalization.isDomain_of_le_nonZeroDivisors T
    (map_le_nonZeroDivisors_of_injective (algebraMap B D) hinj le_rfl)

end SerrePositivity.AlgebraicGeometry
