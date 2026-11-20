module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の有限表示加群の実際の生成全射と関係式行列。
方針：有限生成な核への全射を選び、その包含との合成を有限行列にする。
規約：関係式の列が核全体を生成することを存在証明とともに返す。
使われ方：小行列式の係数中心を有限表示加群から実際に構成する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：有限表示加群には実際の有限自由生成全射と完全な有限関係式行列が存在する。
方針：生成全射を選び、有限表示性による核の有限生成性から有限関係式を選んで行列化する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、環の Noether 性は不要。
使われ方：任意の有限表示加群について小行列式の議論の入力を選ぶ。
-/
theorem exists_finite_presentation_matrix
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ (N t : ℕ) (q : (Fin N → R) →ₗ[R] M) (H : Matrix (Fin N) (Fin t) R),
      Function.Surjective q ∧ Submodule.span R (Set.range H.col) = LinearMap.ker q := by
  classical
  obtain ⟨N, q, hq⟩ := Module.Finite.exists_fin' R M
  have : Module.Finite R (LinearMap.ker q) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker q hq)
  obtain ⟨t, l, hl⟩ := Module.Finite.exists_fin' R (LinearMap.ker q)
  let g := (LinearMap.ker q).subtype.comp l
  let H := LinearMap.toMatrix' g
  refine ⟨N, t, q, H, hq, ?_⟩
  rw [← Matrix.range_mulVecLin]
  have hH : H.mulVecLin = g := Matrix.toLin'_toMatrix' g
  rw [hH]
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact (l y).property
  · intro x hx
    obtain ⟨y, hy⟩ := hl ⟨x, hx⟩
    refine ⟨y, ?_⟩
    change (l y).val = x
    rw [hy]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
