module

public import SerrePositivity.CommutativeAlgebra.CoefficientField
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficientRestriction

/-! # 有限個のp-basis方向を変えた係数写像

核内の有限個の摂動を指定持ち上げの存在定理へ渡し、補集合の像を保持する。
微分の独立性はこの存在定理の仮定にしない。適切な摂動の選択は別の線形代数で行う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K S ι : Type*} [Field K] [CommRing S]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP S p] {b : ι → K}

/-- 核について完備な全射の切断を、有限個の指定p-basis方向だけ摂動する。 -/
theorem IsPBasis.exists_section_of_finitePerturbation (hb : IsPBasis K p b)
    (f : S →+* K) (hf : Function.Surjective f) [IsAdicComplete (RingHom.ker f) S]
    (φ : K →+* S) (hφ : f.comp φ = RingHom.id K)
    (e : Finset ι) (μ : e → RingHom.ker f) :
    ∃ ψ : K →+* S, f.comp ψ = RingHom.id K ∧
      (∀ j : e, ψ (b j) = φ (b j) + μ j) ∧
        ∀ i, i ∉ e → ψ (b i) = φ (b i) := by
  classical
  let β : ι → S := fun i ↦ if hi : i ∈ e then φ (b i) + μ ⟨i, hi⟩ else φ (b i)
  have hβ : ∀ i, f (β i) = b i := by
    intro i
    have hi : f (φ (b i)) = b i := RingHom.congr_fun hφ (b i)
    dsimp [β]
    split_ifs with hie
    · rw [map_add, RingHom.mem_ker.mp (μ ⟨i, hie⟩).property, add_zero, hi]
    · exact hi
  obtain ⟨ψ, hψ, _⟩ := hb.existsUnique_ringHom_lift_of_complete_kernel f hf β hβ
  refine ⟨ψ, hψ.1, ?_, ?_⟩
  · intro j
    simpa [β, j.property] using hψ.2 j
  · intro i hi
    simpa [β, hi] using hψ.2 i

end SerrePositivity
