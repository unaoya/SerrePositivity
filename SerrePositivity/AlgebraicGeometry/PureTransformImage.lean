module

public import SerrePositivity.AlgebraicGeometry.PureTransformModule

/-!
概要：Stacks 0815 の純変換を実際の線形写像の像と比較する。
方針：標的の正則作用と核の冪消滅から核を境界ねじれと同定する。
規約：比較の条件は線形写像の核に課し、平坦化の存在は仮定しない。
使われ方：KST §5 の blowup 上でイデアル加群を自由化する計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
概要：境界元が標的で正則に作用すれば境界ねじれは線形写像の核に入る。
方針：冪による消滅を標的に送り、その正則性で打ち消す。
規約：Stacks 0815、元の加群の正則性は不要。
使われ方：純変換から像への比較写像。
-/
theorem boundaryTorsion_le_ker (g : M →ₗ[R] N) (hf : IsSMulRegular N f) :
    boundaryTorsion f M ≤ LinearMap.ker g := by
  intro m hm
  obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f M m).mp hm
  apply hf.pow n
  dsimp only
  rw [← g.map_smul, hn, g.map_zero, smul_zero]

/--
概要：核が境界の冪で消え、標的で境界元が正則なら核は境界ねじれ。
方針：消滅判定と逆向きの包含を組み合わせる。
規約：Stacks 0815、消滅指数は核の元に依存してよい。
使われ方：第一同型定理による純変換の像との同定。
-/
theorem boundaryTorsion_eq_ker (g : M →ₗ[R] N) (hf : IsSMulRegular N f)
    (hker : ∀ m, g m = 0 → ∃ n : ℕ, f ^ n • m = 0) :
    boundaryTorsion f M = LinearMap.ker g := by
  apply le_antisymm (boundaryTorsion_le_ker f g hf)
  intro m hm
  exact (mem_boundaryTorsion_iff f M m).mpr (hker m hm)

/--
概要：核が境界ねじれの線形写像は純変換とその像の同型を与える。
方針：商の部分加群を同定して第一同型定理を適用する。
規約：Stacks 0815、実際の線形同型を返す。
使われ方：イデアルの純変換の自由化。
-/
def modulePureTransformEquivImage (g : M →ₗ[R] N) (hf : IsSMulRegular N f)
    (hker : ∀ m, g m = 0 → ∃ n : ℕ, f ^ n • m = 0) :
    modulePureTransform f M ≃ₗ[R] LinearMap.range g :=
  (Submodule.quotEquivOfEq _ _ (boundaryTorsion_eq_ker f g hf hker)).trans
    g.quotKerEquivRange

/--
概要：純変換と像の比較同型は元の線形写像を保存する。
方針：商の同定と第一同型定理の代表元上の公式を使う。
規約：Stacks 0815、像から標的への包含を明示する。
使われ方：純変換の自由化と乗法写像の交換式。
-/
theorem modulePureTransformEquivImage_mk (g : M →ₗ[R] N) (hf : IsSMulRegular N f)
    (hker : ∀ m, g m = 0 → ∃ n : ℕ, f ^ n • m = 0) (m : M) :
    (modulePureTransformEquivImage f g hf hker (Submodule.Quotient.mk m) : N) = g m := rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
