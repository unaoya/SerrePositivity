module

public import SerrePositivity.CommutativeAlgebra.Koszul

/-! # 係数つき Koszul 複体と係数変更の可換性 -/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- 任意の複体に対し、Koszul 構成とテンソルによる係数変更を交換する。 -/
noncomputable def baseChangeKoszulOnIso : ∀ {e : ℕ} (x : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    baseChange φ (koszulComplexOn x K) ≅ koszulComplexOn (φ ∘ x) (baseChange φ K)
  | 0, _, _ => Iso.refl _
  | n + 1, x, K => by
      let P := koszulComplexOn (Fin.init x) K
      let a := x (Fin.last n)
      exact CochainComplex.mappingCone.mapHomologicalComplexIso (smulId a P)
        (ModuleCat.extendScalars φ) ≪≫
        eqToIso (congrArg (fun f ↦ CochainComplex.mappingCone f) (baseChange_smulId φ P a)) ≪≫
        (scalarConeFunctor (φ a)).mapIso (baseChangeKoszulOnIso (Fin.init x) K)

end SerrePositivity.Asymptotic
