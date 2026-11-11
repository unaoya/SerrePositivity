module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameRightQuillen
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Actual realization adjoint to cosimplicial Hom

The realization is left Kan extension along the universe-lifted Yoneda
standard simplex. The only colimits assumed have shape Hom universe zero
and object universe v, where v is the Hom universe of the source category.
This hypothesis is explicit; it is not silently inferred from local
presentability in an unrelated universe.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.Realization
variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{0, v} C]

/-- Realization is functorial in the entire cosimplicial source. -/
abbrev family : (SimplexCategory ⥤ C) ⥤ SSet.{v} ⥤ C := uliftYoneda.{v,0,0}.lan

abbrev functor (A : SimplexCategory ⥤ C) : SSet.{v} ⥤ C := uliftYoneda.{v,0,0}.leftKanExtension A

abbrev unit (A : SimplexCategory ⥤ C) : A ⟶ uliftYoneda.{v,0,0} ⋙ functor A :=
  uliftYoneda.{v,0,0}.leftKanExtensionUnit A

/-- Remove the internal Type-level lift in Mathlib's restricted Yoneda. -/
def restrictedIso (A : SimplexCategory ⥤ C) :
    Presheaf.restrictedULiftYoneda.{0} A ≅ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift) (by
    intro n m f
    ext h
    rfl)) (by
      intro Y Z f
      ext n h
      rfl)

/-- The ordinary adjunction uses actual maps of the existing cosimplicial Hom. -/
def adjunction (A : SimplexCategory ⥤ C) : functor A ⊣ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A := by
  let adj := Presheaf.uliftYonedaAdjunction.{0,0,v} (A := A) (functor A) (unit A)
  exact adj.ofNatIsoRight (restrictedIso A)

instance functor_isLeftAdjoint (A : SimplexCategory ⥤ C) : (functor A).IsLeftAdjoint :=
  (adjunction A).isLeftAdjoint

/-- Left Kan extension agrees exactly with A on every standard simplex. -/
def representableIso (A : SimplexCategory ⥤ C) : A ≅ uliftYoneda.{v,0,0} ⋙ functor A := by
  have := Presheaf.isIso_of_isLeftKanExtension.{0,0,v} (functor A) (unit A)
  exact asIso (unit A)

lemma unit_naturality {A B : SimplexCategory ⥤ C} (a : A ⟶ B) :
    a ≫ unit B = unit A ≫ Functor.whiskerLeft uliftYoneda.{v,0,0} (family.map a) :=
  uliftYoneda.{v,0,0}.lanUnit.naturality a

variable [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

include hcof hfib hA hconst

lemma isLeftQuillen : Quillen.IsLeftQuillen (functor A) := by
  have := cosimplicialHom_isRightQuillen hcof hfib A hA hconst
  exact (Quillen.isLeftQuillen_iff_isRightQuillen (adjunction A)).mpr inferInstance

lemma hasPointwiseLeftDerived {H : Type uH} [Category.{vH} H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)] :
    (functor A ⋙ L).HasPointwiseLeftDerivedFunctor (weakEquivalences SSet.{v}) := by
  have := isLeftQuillen hcof hfib A hA hconst
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.Realization
