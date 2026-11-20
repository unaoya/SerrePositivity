module

public import SerrePositivity.AlgebraicGeometry.ProjectiveReductionLift

/-!
概要：KST §5、Stacks 05D3 の剰余全射の核の元の持ち上げ。
方針：代表元の像をイデアル倍の中で持ち上げて差し引く。
規約：全射の始域・終域の平坦性は要求しない。
使われ方：隣接する冪剰余で右逆の整合性の誤差を補正する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：剰余全射の核の任意の元は、元の全射の核の元の剰余である。
方針：代表元の像のイデアル倍にある持ち上げを引いて核へ戻す。
規約：KST §5、Stacks 05D3、仮定は元の全射性のみ。
使われ方：各冪剰余の核の間の全射性と、右逆の整合性の補正。
-/
theorem exists_kernel_preimage_reduceModIdeal
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (I : Ideal R) (y : F ⧸ (I • (⊤ : Submodule R F)))
    (hy : π.reduceModIdeal I y = 0) :
    ∃ k : LinearMap.ker π, (I • (⊤ : Submodule R F)).mkQ k.val = y := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R F)) y
  have hx : π x ∈ I • (⊤ : Submodule R M) := by
    change (I • (⊤ : Submodule R M)).mkQ (π x) = 0 at hy
    change π x ∈ LinearMap.ker (I • (⊤ : Submodule R M)).mkQ at hy
    rwa [Submodule.ker_mkQ] at hy
  obtain ⟨v, hv, hvx⟩ := exists_smul_top_preimage_of_surjective π hπ I (π x) hx
  have hkv : x - v ∈ LinearMap.ker π := by
    change π (x - v) = 0
    rw [map_sub, hvx, sub_self]
  refine ⟨⟨x - v, hkv⟩, ?_⟩
  have hv0 : (I • (⊤ : Submodule R F)).mkQ v = 0 := by
    change v ∈ LinearMap.ker (I • (⊤ : Submodule R F)).mkQ
    rwa [Submodule.ker_mkQ]
  simp only [map_sub, hv0, sub_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
