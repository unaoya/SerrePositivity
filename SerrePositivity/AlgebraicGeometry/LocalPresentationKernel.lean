module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.Module

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の局所自由な対象への表示の核。
方針：射影的な対象への全射の右逆元から核への射影を構成する。
規約：核の有限射影性を実際に導き、Noether 条件は仮定しない。
使われ方：自由な対象の関係式を分裂した自由行列として表示する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R P M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup M]
  [Module R P] [Module R M]

/--
概要：全射の右逆元から構成する核への実際の線形射影。
方針：id - s q の像が核に入ることを示して終域を制限する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、右逆元は明示的に入力する。
使われ方：表示の核を始域の直和因子として扱う。
-/
def presentationKernelProjection (q : P →ₗ[R] M) (s : M →ₗ[R] P)
    (hs : q.comp s = LinearMap.id) : P →ₗ[R] LinearMap.ker q :=
  (LinearMap.id - s.comp q).codRestrict (LinearMap.ker q) (fun x => by
    change q (x - s (q x)) = 0
    have hqs : q (s (q x)) = q x := LinearMap.congr_fun hs (q x)
    rw [map_sub, hqs, sub_self])

/--
概要：核への射影と核の包含の合成は恒等。
方針：核の元への q の値が零であることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：有限性と射影性を表示の核へ移す。
-/
theorem presentationKernelProjection_comp_subtype (q : P →ₗ[R] M) (s : M →ₗ[R] P)
    (hs : q.comp s = LinearMap.id) :
    (presentationKernelProjection q s hs).comp (LinearMap.ker q).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.val - s (q x.val) = x.val
  rw [show q x.val = 0 from x.property, map_zero, sub_zero]

/--
概要：局所環上の有限射影加群から射影加群への全射の核は自由。
方針：実際の右逆元を選び、核を有限射影な直和因子とし、有限平坦加群の局所自由性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、対象の有限性や環の Noether 性は追加仮定しない。
使われ方：局所自由な対象の任意の有限自由表示から自由な関係式の基底を選ぶ。
-/
theorem presentationKernel_free_of_projective [IsLocalRing R]
    [Module.Finite R P] [Module.Projective R P] [Module.Projective R M]
    (q : P →ₗ[R] M) (hq : Function.Surjective q) : Module.Free R (LinearMap.ker q) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let p := presentationKernelProjection q s hs
  have hp : p.comp (LinearMap.ker q).subtype = LinearMap.id :=
    presentationKernelProjection_comp_subtype q s hs
  have : Module.Projective R (LinearMap.ker q) :=
    Module.Projective.of_split (LinearMap.ker q).subtype p hp
  have hpsur : Function.Surjective p := by
    intro x
    exact ⟨x.val, LinearMap.congr_fun hp x⟩
  have : Module.Finite R (LinearMap.ker q) := Module.Finite.of_surjective p hpsur
  exact Module.free_of_flat_of_isLocalRing

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
