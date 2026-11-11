module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Realization
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Actual realization of a simplicial diagram of weights against frames

The index pair (k,n) is a presheaf index. Left Kan extension along its
universe-lifted Yoneda constructs the actual realization of every weight
K-opposite ⥤ SSet. Its right adjoint is the pointwise cosimplicial Hom
functor, naturally in all diagram directions. No enrichment is assumed.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]

/-- Simplicial K-opposite diagrams are presheaves on the actual product index. -/
def weightsEquivalence : (Kᵒᵖ ⥤ SSet.{w}) ≌ ((K × SimplexCategory)ᵒᵖ ⥤ Type w) :=
  Functor.currying.trans ((prodOpEquiv (C := K) (D := SimplexCategory)).symm.congrLeft)

abbrev source (A : K ⥤ SimplexCategory ⥤ C) : K × SimplexCategory ⥤ C := Functor.uncurry.obj A

abbrev presheafRealization (A : K ⥤ SimplexCategory ⥤ C) :
    ((K × SimplexCategory)ᵒᵖ ⥤ Type w) ⥤ C :=
  uliftYoneda.{w,w,w}.leftKanExtension (source K A)

abbrev functor (A : K ⥤ SimplexCategory ⥤ C) : (Kᵒᵖ ⥤ SSet.{w}) ⥤ C :=
  (weightsEquivalence K).functor ⋙ presheafRealization K A

abbrev hom (A : K ⥤ SimplexCategory ⥤ C) : C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  (A.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor).flip

/-- The internal Type-level lift disappears by an actual natural isomorphism. -/
def restrictedIso (A : K ⥤ SimplexCategory ⥤ C) :
    Presheaf.restrictedULiftYoneda.{w} (source K A) ⋙ (weightsEquivalence K).inverse ≅ hom K A :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents (fun k =>
    NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift) (by
      intro n m f
      ext h
      simp [weightsEquivalence, source, hom, Presheaf.restrictedULiftYoneda,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap]
      rfl)) (by
      intro k l f
      ext n h
      simp [weightsEquivalence, source, hom, Presheaf.restrictedULiftYoneda,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap]
      rfl)) (by
    intro Y Z f
    ext k n h
    rfl)

/-- Every simplicial weight diagram has an actual realized object. -/
def adjunction (A : K ⥤ SimplexCategory ⥤ C) : functor K A ⊣ hom K A := by
  let adj := Presheaf.uliftYonedaAdjunction.{0,w,w}
    (A := source K A) (presheafRealization K A)
    (uliftYoneda.{w,w,w}.leftKanExtensionUnit (source K A))
  exact ((weightsEquivalence K).toAdjunction.comp adj).ofNatIsoRight (restrictedIso K A)

instance functor_isLeftAdjoint (A : K ⥤ SimplexCategory ⥤ C) : (functor K A).IsLeftAdjoint :=
  (adjunction K A).isLeftAdjoint

end SerrePositivity.DiagramModel.FrameWeightRealization
