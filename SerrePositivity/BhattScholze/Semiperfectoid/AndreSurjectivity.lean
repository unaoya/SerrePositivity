module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.RootedPerfectoidSurjectivityDescent
public import SerrePositivity.BhattScholze.Inputs.AndreFlatness

/-! # B4の一般全射性：既存André入力に相対的な途中成果

引用なしの降下定理へ既存の名前付きAndré引用を供給する。
この公開定理はsorryAxに依存し、B-S引用を解消したという主張ではない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze

/-- 既存André入力に相対的に、導来p完備な全射商の任意perfectoid化は全射。
一般pねじれ商を含む。André引用のsorryAxが残る条件付き成果であり、B4の引用解消ではない。 -/
theorem surjective_of_isPerfectoidization_of_andre
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  obtain ⟨T, hTring, hTalg, hT, hflat, haic⟩ :=
    Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  let := hTring
  let := hTalg
  let : Algebra R S := q.toAlgebra
  let : Algebra R C := (f.comp q).toAlgebra
  let ff : S →ₐ[R] C := { f with commutes' := fun _ ↦ rfl }
  exact surjective_of_isPerfectoidization_of_aicPerfectoidBaseChange hR hT hq hS
    hflat haic ff hf

end SerrePositivity.BhattScholze
