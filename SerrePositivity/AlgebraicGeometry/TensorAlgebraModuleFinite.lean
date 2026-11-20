module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraModule
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の基底変更加群の基底変更代数上の有限性。
方針：元の有限生成元の 1 ⊗ m が純テンソルを生成することを示す。
規約：基底変更代数の加群構造は明示的に選ぶ。
使われ方：チャート上での Noether 代数上の有限加群の純変換。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：有限 B 加群の基底変更は C ⊗_R B 上有限。
方針：有限 B 生成元の純テンソル像で生成される部分加群に全純テンソルを入れる。
規約：KST §5、Stacks 0815, Theorem 38.30.7、R 上の有限性を仮定しない。
使われ方：有限型代数上の有限加群の基底変更の有限性。
-/
theorem tensorAlgebraModule_finite
    (R B C M : Type*) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Module.Finite B M] :
    letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
    Module.Finite (C ⊗[R] B) (C ⊗[R] M) := by
  classical
  let : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
  let T : Submodule (C ⊗[R] B) (C ⊗[R] M) :=
    Submodule.span (C ⊗[R] B) ((fun m : M => (1 : C) ⊗ₜ[R] m) '' (s : Set M))
  have hspan (m : M) (hm : m ∈ Submodule.span B (s : Set M)) :
      ∀ c : C, c ⊗ₜ[R] m ∈ T := by
    induction hm using Submodule.span_induction with
    | mem m hm =>
      intro c
      have hgen : (1 : C) ⊗ₜ[R] m ∈ T := Submodule.subset_span ⟨m, hm, rfl⟩
      have h := T.smul_mem (c ⊗ₜ[R] (1 : B)) hgen
      simpa only [tensorAlgebraModule_tmul_smul_tmul, mul_one, one_smul] using h
    | zero => intro c; simp
    | add m n hm hn ihm ihn =>
      intro c
      rw [TensorProduct.tmul_add]
      exact T.add_mem (ihm c) (ihn c)
    | smul b m hm ihm =>
      intro c
      have h := T.smul_mem ((1 : C) ⊗ₜ[R] b) (ihm c)
      simpa only [tensorAlgebraModule_tmul_smul_tmul, one_mul] using h
  have hT : T = ⊤ := by
    apply top_unique
    intro z _
    induction z using TensorProduct.inductionOn with
    | tmul c m => exact hspan m (by rw [hs]; trivial) c
    | add x y hx hy => exact T.add_mem (hx trivial) (hy trivial)
  have hfg : T.FG := Submodule.fg_span (s.finite_toSet.image _)
  exact Module.Finite.of_fg_top (hT ▸ hfg)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
