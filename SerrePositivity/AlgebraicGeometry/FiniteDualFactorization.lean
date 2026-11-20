module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.Module.LinearMap.End

/-!
概要：KST §5、Stacks 05DP・059X の有限自由双対像から任意の加群値の前合成像への移送。
方針：各双対座標を持ち上げ、その有限和で任意の値域への因子化を作る。
規約：基礎環の Noether 性と値域の有限性・平坦性は不要。
使われ方：係数環値の双対像安定化を任意の Hom 逆系の像安定化へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：有限自由な中間加群の双対像の包含から、任意の加群値の実際の線形因子化が得られる。
方針：双対基底の各座標の持ち上げを選び、像の基底元の値との積の和を取る。
規約：KST §5、Stacks 05DP・059X、もう一方の中間加群の有限性は不要。
使われ方：双対像の安定化を任意の値域への前合成に適用する。
-/
theorem linearMap_factorization_of_dual_range_le
    {R U V W N ι : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [AddCommGroup N] [Module R N] [Finite ι]
    (b : Module.Basis ι R V) (f : U →ₗ[R] V) (g : U →ₗ[R] W)
    (hdual : LinearMap.range f.dualMap ≤ LinearMap.range g.dualMap) (φ : V →ₗ[R] N) :
    ∃ ψ : W →ₗ[R] N, ψ.comp g = φ.comp f := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hex (i : ι) : ∃ ψ : Module.Dual R W, g.dualMap ψ = f.dualMap (b.coord i) :=
    hdual ⟨b.coord i, rfl⟩
  choose ψ hψ using hex
  refine ⟨∑ i, (ψ i).smulRight (φ (b i)), ?_⟩
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
  calc
    (∑ i, ψ i (g x) • φ (b i)) = ∑ i, b.repr (f x) i • φ (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := congrArg (fun ε : Module.Dual R U => ε x) (hψ i)
      have hval : ψ i (g x) = b.repr (f x) i := by
        simpa only [LinearMap.dualMap_apply, Module.Basis.coord_apply] using h
      rw [hval]
    _ = φ (∑ i, b.repr (f x) i • b i) := by simp only [map_sum, map_smul]
    _ = φ (f x) := congrArg φ (b.sum_repr (f x))

/--
概要：二つの有限自由中間加群への双対像が等しいなら、任意の値域への前合成像は一致する。
方針：双対像の両方向の包含から実際の因子化を取り、指定写像との等式を合成する。
規約：KST §5、Stacks 05DP・059X、値域の宇宙・有限性は任意。
使われ方：有限自由列の任意の加群値の Hom 逆系の像の安定化。
-/
theorem linearMap_factorization_iff_of_dual_ranges_eq
    {R U V W N ι κ : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [AddCommGroup N] [Module R N] [Finite ι] [Finite κ]
    (b : Module.Basis ι R V) (c : Module.Basis κ R W)
    (f : U →ₗ[R] V) (g : U →ₗ[R] W)
    (hdual : LinearMap.range f.dualMap = LinearMap.range g.dualMap) (h : U →ₗ[R] N) :
    (∃ φ : V →ₗ[R] N, φ.comp f = h) ↔ ∃ ψ : W →ₗ[R] N, ψ.comp g = h := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := linearMap_factorization_of_dual_range_le b f g hdual.le φ
    exact ⟨ψ, hψ.trans hφ⟩
  · rintro ⟨ψ, hψ⟩
    obtain ⟨φ, hφ⟩ := linearMap_factorization_of_dual_range_le c g f hdual.ge ψ
    exact ⟨φ, hφ.trans hψ⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
