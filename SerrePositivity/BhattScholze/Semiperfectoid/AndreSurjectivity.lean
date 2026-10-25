module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.RootedPerfectoidSurjectivityDescent
public import SerrePositivity.BhattScholze.Andre.AndreFlatness

/-! # B4の一般全射性：André の補題による原典の証明

André の補題（Thm 7.14、`Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、
証明済み）による、原典の Thm 7.4 の証明。
絶対整閉な perfectoid 環への p 完全忠実平坦な拡大で全射性を得て、元の基底へ降下する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze

/-- André の補題（Thm 7.14、証明済み）による、原典の Thm 7.4 の証明。
導来p完備な全射商の任意perfectoid化は全射であり、一般pねじれ商を含む。 -/
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
