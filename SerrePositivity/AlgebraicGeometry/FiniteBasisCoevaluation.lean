module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
概要：KST §5、Stacks 05DP・059X の Mittag–Leffler 判定に使う有限基底の余評価計算。
方針：基底と双対座標から作るテンソルの各座標を計算し、双対写像の像の消滅と比較する。
規約：試験加群の有限性・平坦性と基礎環の Noether 性は不要。
使われ方：双対像による商加群の積を Mittag–Leffler 性の試験族として使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R U V N ι κ : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup N] [Module R N] [Fintype ι] [Finite κ]

/--
概要：有限基底と双対からの線形写像により作る実際のテンソル。
方針：基底元と双対座標の像の純テンソルを有限和する。
規約：KST §5、Stacks 05DP・059X、商加群と積加群の両方を係数先に取れる。
使われ方：双対像の包含をテンソルの消滅で判定する。
-/
def basisMappedCoevaluationTensor (b : Module.Basis ι R U) (ε : Module.Dual R U →ₗ[R] N) :
    U ⊗[R] N := ∑ i, b i ⊗ₜ[R] ε (b.coord i)

/--
概要：基底の余評価テンソルの線形像が零であることは、双対写像の像が係数写像で消えることと同値。
方針：終域の各基底座標を係数写像での双対行の評価と同定し、双対基底の生成性を使う。
規約：KST §5、Stacks 05DP・059X、両基底は有限、試験加群は任意。
使われ方：双対像の商とその積に対する有限自由段階の零判定。
-/
theorem basisMappedCoevaluationTensor_rTensor_eq_zero_iff
    (b : Module.Basis ι R U) (c : Module.Basis κ R V)
    (f : U →ₗ[R] V) (ε : Module.Dual R U →ₗ[R] N) :
    f.rTensor N (basisMappedCoevaluationTensor b ε) = 0 ↔
      LinearMap.range f.dualMap ≤ LinearMap.ker ε := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let E : V ⊗[R] N ≃ₗ[R] (κ →₀ N) := TensorProduct.equivFinsuppOfBasisLeft c
  have hcoord (j : κ) :
      E (f.rTensor N (basisMappedCoevaluationTensor b ε)) j = ε ((c.coord j).comp f) := by
    calc
      E (f.rTensor N (basisMappedCoevaluationTensor b ε)) j =
          ∑ i, c.repr (f (b i)) j • ε (b.coord i) := by
        simp [E, basisMappedCoevaluationTensor]
      _ = ε (∑ i, c.repr (f (b i)) j • b.coord i) := by simp only [map_sum, map_smul]
      _ = ε ((c.coord j).comp f) := by
        congr 1
        exact b.sum_dual_apply_smul_coord ((c.coord j).comp f)
  constructor
  · intro hx
    have hrow (j : κ) : (c.coord j).comp f ∈ LinearMap.ker ε := by
      change ε ((c.coord j).comp f) = 0
      rw [← hcoord j, hx, map_zero, Finsupp.zero_apply]
    rintro _ ⟨φ, rfl⟩
    rw [← c.sum_dual_apply_smul_coord φ, map_sum]
    apply (LinearMap.ker ε).sum_mem
    intro j _
    rw [map_smul]
    change φ (c j) • ((c.coord j).comp f) ∈ LinearMap.ker ε
    exact (LinearMap.ker ε).smul_mem (φ (c j)) (hrow j)
  · intro h
    apply E.injective
    ext j
    rw [map_zero, Finsupp.zero_apply, hcoord j]
    exact h ⟨c.coord j, rfl⟩

/--
概要：双対からの写像の積で作った余評価テンソルの各成分は、各写像で作った余評価テンソル。
方針：有限和と純テンソル上で積比較写像を計算する。
規約：KST §5、Stacks 05DP・059X、試験族の添字は有限とは限らない。
使われ方：Mittag–Leffler 性の積比較の単射性を双対像の試験族へ適用する。
-/
theorem basisMappedCoevaluationTensor_piRightHom
    {J : Type*} (P : J → Type*) [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
    (b : Module.Basis ι R U) (ε : ∀ j, Module.Dual R U →ₗ[R] P j) (j : J) :
    TensorProduct.piRightHom R R U P
        (basisMappedCoevaluationTensor b (LinearMap.pi ε)) j =
      basisMappedCoevaluationTensor b (ε j) := by
  simp [basisMappedCoevaluationTensor, map_sum, Finset.sum_apply]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
