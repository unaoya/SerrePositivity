module

public import SerrePositivity.AlgebraicGeometry.LocalPresentationKernel
public import SerrePositivity.AlgebraicGeometry.SplitMatrixMinorIdeal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の局所自由対象の関係式の実際の分裂行列。
方針：核への射影と局所環上の自由な核の基底から行列とその左逆元を作る。
規約：表示の分裂を仮定せず、対象の射影性から構成する。
使われ方：自由な対象の任意の有限関係式行列の小行列式条件を導く。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：局所環上の有限自由加群から射影加群への全射の核は、実際の左逆元を持つ有限行列で表せる。
方針：右逆元から核への射影を作り、自由な核の有限基底を座標化する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、環の Noether 性は不要。
使われ方：関係式の小行列式の単位条件と消滅条件を実在する分裂から導く。
-/
theorem exists_split_matrix_for_local_presentation_kernel
    {R M m : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Fintype m]
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) :
    ∃ (k : ℕ) (T : Matrix m (Fin k) R) (S : Matrix (Fin k) m R),
      S * T = 1 ∧ Submodule.span R (Set.range T.col) = LinearMap.ker q := by
  classical
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let p := presentationKernelProjection q s hs
  have hp : p.comp (LinearMap.ker q).subtype = LinearMap.id :=
    presentationKernelProjection_comp_subtype q s hs
  have hpsur : Function.Surjective p := fun x => ⟨x.val, LinearMap.congr_fun hp x⟩
  have : Module.Finite R (LinearMap.ker q) := Module.Finite.of_surjective p hpsur
  have : Module.Free R (LinearMap.ker q) := presentationKernel_free_of_projective q hq
  let ι := Module.Free.ChooseBasisIndex R (LinearMap.ker q)
  let : Fintype ι := Fintype.ofFinite ι
  let k := Fintype.card ι
  let e₀ := (Module.Free.chooseBasis R (LinearMap.ker q)).repr.trans
    (Finsupp.linearEquivFunOnFinite R R ι)
  let e : LinearMap.ker q ≃ₗ[R] (Fin k → R) :=
    e₀.trans (LinearEquiv.funCongrLeft R R (Fintype.equivFin ι).symm)
  let t := (LinearMap.ker q).subtype.comp e.symm.toLinearMap
  let z := e.toLinearMap.comp p
  have hzt : z.comp t = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e (p (e.symm x).val) = x
    have hx : p (e.symm x).val = e.symm x := LinearMap.congr_fun hp (e.symm x)
    rw [hx, e.apply_symm_apply]
  let T := LinearMap.toMatrix' t
  let S := LinearMap.toMatrix' z
  refine ⟨k, T, S, ?_, ?_⟩
  · change LinearMap.toMatrix' z * LinearMap.toMatrix' t = 1
    rw [← LinearMap.toMatrix'_comp, hzt, LinearMap.toMatrix'_id]
  · rw [← Matrix.range_mulVecLin]
    have hT : T.mulVecLin = t := Matrix.toLin'_toMatrix' t
    rw [hT]
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      exact (e.symm a).property
    · intro x hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      change (e.symm (e ⟨x, hx⟩)).val = x
      rw [e.symm_apply_apply]

/--
概要：射影的な対象の局所的な有限自由表示の関係式行列には、小行列式の単位次数とその後の消滅がある。
方針：核の実際の分裂行列を構成し、同じ列部分加群による不変性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、関係式の像が核全体を生成することを明示する。
使われ方：平坦化の境界外での Fitting 型の条件を導く。
-/
theorem exists_minor_pattern_of_projective_presentation
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Finite m] [Finite n]
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (H : Matrix m n R)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q) :
    ∃ k : ℕ, matrixMinorIdeal H k = ⊤ ∧ ∀ j, k < j → matrixMinorIdeal H j = ⊥ := by
  let : Fintype m := Fintype.ofFinite m
  obtain ⟨k, T, S, hST, hT⟩ := exists_split_matrix_for_local_presentation_kernel q hq
  exact ⟨k, matrixMinorIdeal_of_split_columnSpan H T S hST (hH.trans hT.symm)⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
