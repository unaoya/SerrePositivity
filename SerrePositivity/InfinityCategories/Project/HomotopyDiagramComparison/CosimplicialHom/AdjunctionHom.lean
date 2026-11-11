module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom

/-!
分割で生成：docstring を書き直すこと
 # The actual simplicial Hom isomorphism of an ordinary adjunction

Hom universes may differ. Both simplicial sets are lifted to their common
universe; in equal hom universes an unlifted comparison is also provided.
All comparisons are natural in both the cosimplicial object and target.
-/

@[expose] public section
universe vC uC vD uD v
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The componentwise adjunction isomorphism, with independent Hom universes. -/
def adjunctionHomIso (A : SimplexCategory ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ L) ⋙ SSet.uliftFunctor.{vC,vD} ≅
      R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A ⋙ SSet.uliftFunctor.{vD,vC} :=
  NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun n => Equiv.toIso
      (Equiv.ulift.trans ((adj.homEquiv (A.obj n.unop) Y).trans Equiv.ulift.symm))) (by
        intro n m f
        ext h
        apply ULift.ext
        exact adj.homEquiv_naturality_left (A.map f.unop) h.down)) (by
    intro X Y f
    ext n h
    apply ULift.ext
    exact adj.homEquiv_naturality_right h.down f)

@[reassoc]
lemma adjunctionHomIso_source_naturality {A B : SimplexCategory ⥤ C} (a : A ⟶ B) :
    Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerRight a L))
        SSet.uliftFunctor.{vC,vD} ≫ (adjunctionHomIso adj A).hom =
      (adjunctionHomIso adj B).hom ≫
        Functor.whiskerLeft R
          (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a) SSet.uliftFunctor.{vD,vC}) := by
  ext Y n h
  apply ULift.ext
  exact adj.homEquiv_naturality_left (a.app n.unop) h.down

section SameUniverse
variable {C' : Type uC} [Category.{v} C'] {D' : Type uD} [Category.{v} D']
  {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')

def adjunctionHomIsoSameUniverse (A : SimplexCategory ⥤ C') :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ L') ≅ R' ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A :=
  NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun n => Equiv.toIso (adj'.homEquiv (A.obj n.unop) Y)) (by
      intro n m f
      ext h
      exact adj'.homEquiv_naturality_left (A.map f.unop) h)) (by
    intro X Y f
    ext n h
    exact adj'.homEquiv_naturality_right h f)

@[reassoc]
lemma adjunctionHomIsoSameUniverse_source_naturality {A B : SimplexCategory ⥤ C'}
    (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerRight a L') ≫ (adjunctionHomIsoSameUniverse adj' A).hom =
      (adjunctionHomIsoSameUniverse adj' B).hom ≫
        Functor.whiskerLeft R' (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a) := by
  ext Y n h
  exact adj'.homEquiv_naturality_left (a.app n.unop) h

end SameUniverse
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
