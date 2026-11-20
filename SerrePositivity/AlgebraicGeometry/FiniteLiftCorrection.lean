module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FiniteDualFactorization

/-!
概要：KST §5、Stacks 05DP・059X の全射への持ち上げの差を核値の写像で補正する補題。
方針：二つの持ち上げの差を核へ送り、双対像の包含による有限自由因子化で補正する。
規約：全射性の存在はこの補題には不要で、実際に与えられた二写像を補正する。
使われ方：安定した Hom 像から持ち上げの集合の逆系の Mittag–Leffler 性を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：有限自由段階の双対像の包含により、基底上で一致する二つの持ち上げを初段で一致するよう補正できる。
方針：持ち上げの差の核への制限を後段へ因子化し、後段の持ち上げに加える。
規約：KST §5、Stacks 05DP・059X、値域と基礎環の Noether 性・平坦性は不要。
使われ方：有限自由近似列の各段階での持ち上げの整合性を確保する。
-/
theorem exists_compatible_lift_of_dual_range_le
    {R U V W E M ι : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] [Finite ι]
    (b : Module.Basis ι R V) (f : U →ₗ[R] V) (g : U →ₗ[R] W) (t : V →ₗ[R] W)
    (ht : t.comp f = g) (hdual : LinearMap.range f.dualMap ≤ LinearMap.range g.dualMap)
    (π : E →ₗ[R] M) (Φ : V →ₗ[R] E) (Ψ : W →ₗ[R] E)
    (hcomp : π.comp Φ = (π.comp Ψ).comp t) :
    ∃ Ψ' : W →ₗ[R] E, π.comp Ψ' = π.comp Ψ ∧ Ψ'.comp g = Φ.comp f := by
  have hδ (v : V) : (Φ - Ψ.comp t) v ∈ LinearMap.ker π := by
    change π (Φ v - Ψ (t v)) = 0
    have hv := congrArg (fun h : V →ₗ[R] M => h v) hcomp
    change π (Φ v) = π (Ψ (t v)) at hv
    rw [map_sub, hv, sub_self]
  let δ : V →ₗ[R] LinearMap.ker π := (Φ - Ψ.comp t).codRestrict (LinearMap.ker π) hδ
  obtain ⟨η, hη⟩ := linearMap_factorization_of_dual_range_le b f g hdual δ
  refine ⟨Ψ + (LinearMap.ker π).subtype.comp η, ?_, ?_⟩
  · ext w
    change π (Ψ w + (η w).val) = π (Ψ w)
    have hw : π (η w).val = 0 := (η w).property
    rw [map_add, hw, add_zero]
  · ext u
    have hu := congrArg (fun h : U →ₗ[R] LinearMap.ker π => h u) hη
    have hval : (η (g u)).val = Φ (f u) - Ψ (t (f u)) := congrArg Subtype.val hu
    have htu : t (f u) = g u := congrArg (fun h : U →ₗ[R] W => h u) ht
    rw [htu] at hval
    change Ψ (g u) + (η (g u)).val = Φ (f u)
    rw [hval]
    rw [add_comm, sub_add_cancel]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
