module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalPresentationKernel
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の表示の核と対象の実際の直積分解。
方針：右逆元と核への射影を互いに逆な線形写像に組み合わせる。
規約：分解は実際の線形同型で与え、階数の等式だけを仮定しない。
使われ方：小行列式の次数と対象の自由階数の関係を特定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R P M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup M]
  [Module R P] [Module R M]

/--
概要：右逆元を持つ表示の始域は、核と対象の直積と実際に線形同型。
方針：核の包含と右逆元の和を、核への射影と表示写像の組で逆にする。
規約：KST §5、Stacks 0810, Lemma 38.30.2、局所環や有限性はこの構成には不要。
使われ方：関係式の自由階数と対象の自由階数を合計する。
-/
def presentationKernelProdEquiv (q : P →ₗ[R] M) (s : M →ₗ[R] P)
    (hs : q.comp s = LinearMap.id) : (LinearMap.ker q × M) ≃ₗ[R] P := by
  let f := (LinearMap.ker q).subtype.coprod s
  let g := (presentationKernelProjection q s hs).prod q
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change x - s (q x) + s (q x) = x
    exact sub_add_cancel x (s (q x))
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hx : q x.1.val = 0 := x.1.property
    have hqs : q (s x.2) = x.2 := LinearMap.congr_fun hs x.2
    apply Prod.ext
    · apply Subtype.ext
      change x.1.val + s x.2 - s (q (x.1.val + s x.2)) = x.1.val
      rw [map_add, hx, zero_add, hqs, add_sub_cancel_right]
    · change q (x.1.val + s x.2) = x.2
      rw [map_add, hx, hqs, zero_add]
  exact LinearEquiv.ofLinearMap f g hfg hgf

/--
概要：局所環上の有限射影な表示の始域の階数は、核と対象の階数の和。
方針：実際の右逆元と直積分解を構成し、各加群の有限自由性から階数を計算する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、対象の有限性は表示の全射から導く。
使われ方：小行列式の単位次数を生成元数と対象の自由階数から特定する。
-/
theorem presentationKernel_finrank_add [IsLocalRing R]
    [Module.Finite R P] [Module.Projective R P] [Module.Projective R M]
    (q : P →ₗ[R] M) (hq : Function.Surjective q) :
    Module.finrank R (LinearMap.ker q) + Module.finrank R M = Module.finrank R P := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let p := presentationKernelProjection q s hs
  have hp : p.comp (LinearMap.ker q).subtype = LinearMap.id :=
    presentationKernelProjection_comp_subtype q s hs
  have : Module.Finite R (LinearMap.ker q) := Module.Finite.of_surjective p
    (fun x => ⟨x.val, LinearMap.congr_fun hp x⟩)
  have : Module.Finite R M := Module.Finite.of_surjective q hq
  have : Module.Free R (LinearMap.ker q) := presentationKernel_free_of_projective q hq
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  simpa only [Module.finrank_prod] using (presentationKernelProdEquiv q s hs).finrank_eq

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
