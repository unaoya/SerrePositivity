module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.F1.UniversePinchedHom
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.CoherentPrismEvaluation

/-! 実 pinched Hom 族の区間評価は、元の族と端点を保つ宇宙移送と可換。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma dgGluingUliftPinchedIntervalFamily {K X : SSet.{u}} {x y : X _⦋0⦌}
    (f : K ⟶ pinchedHom x y) :
    dgGluingUliftSimplexFamily.{u, v} 1
        (intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y)) =
      intervalMappingUncurry
        (((SSet.uliftFunctor.{v, u}).map f ≫ (uliftPinchedHomIso x y).hom) ≫
          pinchedHomToIntervalMappingSpace
            (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) (ULift.up y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨a⟩⟩
  change ULift.up ((intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y)).app
      (Opposite.op ⦋n⦌) (ULift.up t.down, a)) =
    (intervalMappingUncurry
      (((SSet.uliftFunctor.{v, u}).map f ≫ (uliftPinchedHomIso.{u, v} x y).hom) ≫
        pinchedHomToIntervalMappingSpace
          (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) (ULift.up y))).app
      (Opposite.op ⦋n⦌) (t, ULift.up a)
  have h₀ := pinchedHomToIntervalMappingSpace_evaluate.{u} f a
    (ULift.up t.down : (Δ[1] : SSet.{u}) _⦋n⦌)
  have h₁ := pinchedHomToIntervalMappingSpace_evaluate.{max u v}
    (X := (SSet.uliftFunctor.{v, u}).obj X)
    ((SSet.uliftFunctor.{v, u}).map f ≫ (uliftPinchedHomIso.{u, v} x y).hom)
    (ULift.up a) t
  rw [h₀, h₁]
  rfl

end SerrePositivity.InfinityCategories
