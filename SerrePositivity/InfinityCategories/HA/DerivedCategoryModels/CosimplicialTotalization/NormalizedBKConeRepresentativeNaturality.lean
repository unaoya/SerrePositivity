module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanComparisonNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeComposition

/-!
概要：指定BK錐の同じ実複体代表は、元の全図式射の後合成に自然。
方針：既存ofHomの単射性で、同じHom–Tot比較の自然性を閉元に適用する。
規約：IS-W2 D01の既存構成の自然性・合成則。
使われ方：HA 1.2.4、指定錐の全高次単体のパラメータ輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable {A : Type u} [CommRing A]

/-- 同じ係数図式射から得る、BK錐代表の標的複体の射。 -/
def normalizedBKConeTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X)) ⟶
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj Y)) :=
  (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).map
    (Functor.whiskerLeft (opOpEquivalence SimplexCategory).functor
      ((homDiagramFunctor P).map f))

/-- 元の指定複体代表は、同じ図式射とTot射の像を保つ。 -/
theorem normalizedBousfieldKanRepresentative_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    (g : P ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanRepresentative P X g ≫ normalizedBKConeTargetMap P f =
      normalizedBousfieldKanRepresentative P Y (g ≫ (productTotalFunctor A).map f) := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, normalizedBousfieldKanRepresentative_cochain,
    normalizedBousfieldKanRepresentative_cochain]
  have h := congrArg (fun t => t (Cochain.ofHom g))
    (congrArg (fun t => t.f 0) (homToNormalizedBousfieldKan_naturality P f))
  change (homToNormalizedBousfieldKan P Y).f 0
      ((Cochain.ofHom g).comp (Cochain.ofHom ((productTotalFunctor A).map f)) (add_zero 0)) =
    ((homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom g)).comp
      (Cochain.ofHom (normalizedBKConeTargetMap P f)) (add_zero 0) at h
  rw [← Cochain.ofHom_comp] at h
  exact h.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
