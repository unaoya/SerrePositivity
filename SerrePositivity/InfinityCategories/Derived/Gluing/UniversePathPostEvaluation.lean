module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePathPullback

/-! 実区間族の持ち上げ・係数後合成・端点評価は、同じ端点番号で可換。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet HomotopyLimits
open scoped Simplicial

lemma dgGluingIntervalPost_evaluate {K L : SSet.{u}} (f : K ⟶ L) (j : Fin 2) :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) =
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) ≫ f :=
  (F2.intervalEndpointNatTrans j).naturality f

lemma dgGluingUliftIntervalPost_evaluate {A K : SSet.{u}} {L : SSet.{max u v}}
    (h : A ⟶ (ihom (Δ[1] : SSet.{u})).obj K)
    (f : (SSet.uliftFunctor.{v, u}).obj K ⟶ L) (j : Fin 2) :
    ((SSet.uliftFunctor.{v, u}).map h ≫ (uliftIntervalHomIso K).hom ≫
        (ihom (Δ[1] : SSet.{max u v})).map f) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) =
    (SSet.uliftFunctor.{v, u}).map
        (h ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) ≫ f := by
  simp only [Category.assoc, dgGluingIntervalPost_evaluate]
  rw [← Category.assoc (uliftIntervalHomIso K).hom,
    uliftIntervalHomIso_hom_evaluate, ← Category.assoc, ← Functor.map_comp]

end SerrePositivity.InfinityCategories
