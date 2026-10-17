module

public import SerrePositivity.CLMST.Prop247ProductUniversality
public import SerrePositivity.CLMST.Prop247RankTargetComparison
public import SerrePositivity.BhattScholze.Inputs.Perfectoidization

/-! # Prop 2.4.7：実 rank 成分単位の直積の普遍性

元の有限係数から直積始域の整性を得て、既存 B-I で全体の単位を一つ選ぶ。
成分単位の直積そのものの普遍性は、前工程の指定全体単位による証明から得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の有限係数と各指定普遍単位から、実 rank 直積単位の普遍性を供給する。
直積単位の普遍性を追加仮定にせず、既存 B-I のみを存在選択に使用する。 -/
theorem prop247_rankProductUnit_isPerfectoidization_of_finite_coefficients
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {ι : Type} [Finite ι] (T P : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] [∀ i, Module.Finite R (T i)]
    [∀ i, CommRing (P i)] [∀ i, Algebra R (P i)]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (β : ∀ i, T i ⊗[R] S →ₐ[R] P i)
    (hβ : ∀ i, IsPerfectoidization p (β i).toRingHom) :
    IsPerfectoidization p (prop247_rankProductUnit R S T P β).toRingHom := by
  letI : Module.Finite R ((i : ι) → T i ⊗[R] S) := inferInstance
  obtain ⟨C, hC, f, hf⟩ := BhattScholze.Inputs.exists_perfectoidization_of_integral R
    ((i : ι) → T i ⊗[R] S) p hR
  letI := hC
  change IsPerfectoidization p (prop247_productPerfectoidizationUnit
    (fun i => T i ⊗[R] S) P (fun i => (β i).toRingHom))
  exact prop247_productUnit_isPerfectoidization_of_specified (fun i => T i ⊗[R] S) P
    (fun i => (β i).toRingHom) p hβ C f hf

end SerrePositivity.CLMST
