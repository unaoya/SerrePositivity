module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ProjectiveReductionLift
public import SerrePositivity.AlgebraicGeometry.NilpotentKernelSection

/-!
概要：KST §5、Stacks 05CG, Lemma 10.77.7 の冪零剰余からの平坦加群の射影性。
方針：剰余右逆を持ち上げた自己準同型の冪で核を消し、自由全射の実際の右逆を作る。
規約：基礎環の Noether 性も加群の有限性も仮定しない。
使われ方：Stacks 05D3 の各冪剰余での射影性。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：平坦な終域の冪零剰余が射影的なら、射影的な始域からの任意の全射に右逆がある。
方針：剰余の右逆を持ち上げ、平坦性による核とイデアル倍の交わりを使って核を消す。
規約：KST §5、Stacks 05CG、冪零性は具体的な指数で与える。
使われ方：元の終域の射影性と、各冪剰余の全射の分裂。
-/
theorem exists_section_of_projective_nilpotent_reduction
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F] [Module.Projective R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (I : Ideal R)
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (n : ℕ) (hn : I ^ n = 0) : ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id := by
  let QF := I • (⊤ : Submodule R F)
  let QM := I • (⊤ : Submodule R M)
  have hbar : Function.Surjective (π.reduceModIdeal I) := by
    intro m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective QM m
    obtain ⟨x, rfl⟩ := hπ m
    exact ⟨QF.mkQ x, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (π.reduceModIdeal I) LinearMap.id hbar
  obtain ⟨e, he, hebar⟩ := exists_endomorphism_lifting_reduction_section π hπ I s hs
  apply exists_section_of_nilpotent_kernel_endomorphism π hπ I n hn e he
  intro x
  have heker : e x.val ∈ LinearMap.ker π := by
    change π (e x.val) = 0
    have hk : π x.val = 0 := x.property
    exact (congrArg (fun f => f x.val) he).trans hk
  let y : LinearMap.ker π := ⟨e x.val, heker⟩
  have hzero : QF.mkQ (e x.val) = 0 := by
    have hx := congrArg (fun f => f x.val) hebar
    change QF.mkQ (e x.val) = s (QM.mkQ (π x.val)) at hx
    rw [x.property, map_zero, map_zero] at hx
    exact hx
  have hy : y ∈ (I • (⊤ : Submodule R F)).comap (LinearMap.ker π).subtype := by
    change e x.val ∈ I • (⊤ : Submodule R F)
    change e x.val ∈ LinearMap.ker QF.mkQ at hzero
    rwa [Submodule.ker_mkQ] at hzero
  rw [smul_top_comap_kernel_subtype_of_flat π hπ I] at hy
  exact ⟨y, hy, rfl⟩

/--
概要：冪零イデアルを法とする剰余が射影的な平坦加群は射影的。
方針：元の加群を添字とする自由全射に、構成済みの右逆を与える。
規約：KST §5、Stacks 05CG, Lemma 10.77.7、有限生成性を要求しない。
使われ方：完備化の分裂を作るための各冪剰余の射影性。
-/
theorem projective_of_flat_of_projective_nilpotent_reduction
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I : Ideal R) [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (n : ℕ) (hn : I ^ n = 0) : Module.Projective R M := by
  apply Module.projective_def'.mpr
  exact exists_section_of_projective_nilpotent_reduction
    (Finsupp.linearCombination R (id : M → M))
    (Finsupp.linearCombination_surjective R Function.surjective_id) I n hn

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
