module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.Algebra.Module.FinitePresentation

/-!
概要：Stacks 0815 の Noether 特殊形に使う有限表示加群の局所化同型の分母消去。
方針：同型の両射を持ち上げ、合成の誤差を一様な分母で消す。
規約：平坦化中心の存在を仮定せず、実際の線形写像と合成式を返す。
使われ方：KST §5 の平坦化の階数一自由な有限加群の特殊形。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (S : Submonoid R)
  {M N M' N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  [Module.FinitePresentation R M] [Module.FinitePresentation R N]
  (μ : M →ₗ[R] M') (ν : N →ₗ[R] N')
  [IsLocalizedModule S μ] [IsLocalizedModule S ν]

include μ ν

/--
概要：局所化で同型な有限表示加群の間に分母倍の互いに逆な写像を作る。
方針：両射を有限表示性で持ち上げ、有限生成性で合成の誤差を消す。
規約：Stacks 0815、同じ s が両方の合成に使われる。
使われ方：階数一の有限加群をイデアル加群へ比較する証明。
-/
theorem exists_localization_isogeny (e : M' ≃ₗ[R] N') :
    ∃ (s : S) (g : M →ₗ[R] N) (h : N →ₗ[R] M),
      h.comp g = s.val • LinearMap.id ∧ g.comp h = s.val • LinearMap.id := by
  obtain ⟨g, s, hg⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S ν (e.toLinearMap.comp μ)
  obtain ⟨h, t, hh⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S μ (e.symm.toLinearMap.comp ν)
  have hg' (m : M) : ν (g m) = s.val • e (μ m) := LinearMap.congr_fun hg m
  have hh' (n : N) : μ (h n) = t.val • e.symm (ν n) := LinearMap.congr_fun hh n
  have hleft : μ.comp (h.comp g) = μ.comp ((t.val * s.val) • LinearMap.id) := by
    ext m
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hh', hg', e.symm.map_smul, e.symm_apply_apply, mul_smul, μ.map_smul]
    simp only [μ.map_smul]
  have hright : ν.comp (g.comp h) = ν.comp ((t.val * s.val) • LinearMap.id) := by
    ext n
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hg', hh', e.map_smul, e.apply_symm_apply, mul_smul, ν.map_smul]
    simpa only [ν.map_smul] using smul_comm s.val t.val (ν n)
  obtain ⟨u, hu⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S μ (h.comp g) ((t.val * s.val) • LinearMap.id) hleft
  obtain ⟨v, hv⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S ν (g.comp h) ((t.val * s.val) • LinearMap.id) hright
  refine ⟨u * v * t * s, g, (u.val * v.val) • h, ?_, ?_⟩
  · calc
      (((u.val * v.val) • h).comp g) = v.val • (u.val • (h.comp g)) := by
        ext m
        change (u.val * v.val) • h (g m) = v.val • u.val • h (g m)
        rw [mul_smul]
        exact smul_comm _ _ _
      _ = v.val • (u.val • ((t.val * s.val) • LinearMap.id)) := by
        exact congrArg (fun k => v.val • k) hu
      _ = (u * v * t * s).val • LinearMap.id := by
        simp [smul_smul, mul_comm, mul_left_comm]
  · calc
      g.comp ((u.val * v.val) • h) = u.val • (v.val • (g.comp h)) := by
        ext n
        simp [mul_smul]
      _ = u.val • (v.val • ((t.val * s.val) • LinearMap.id)) := by
        exact congrArg (fun k => u.val • k) hv
      _ = (u * v * t * s).val • LinearMap.id := by
        simp [smul_smul, mul_assoc]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
