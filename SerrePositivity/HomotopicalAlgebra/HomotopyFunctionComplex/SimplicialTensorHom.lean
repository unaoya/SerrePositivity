module

public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # Actual enriched Map as Hom on the standard tensor cosimplicial family

Tensor representability followed by simplicial Yoneda gives an isomorphism
of actual simplicial sets. It is natural in both ordinary variables, not
just a bijection degree by degree. No model structure is assumed here.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory SSet.{v} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C)

abbrev tensorCosimplicialFamily : C ⥤ (SimplexCategory ⥤ C) :=
  S.tensor.flip ⋙ (Functor.whiskeringLeft SimplexCategory SSet.{v} C).obj SSet.stdSimplex

def simplexTensorHomEquiv (X Y : C) (n : SimplexCategory) :
    (((tensorCosimplicialFamily S).obj X).obj n ⟶ Y) ≃
      (X ⟶[SSet.{v}] Y).obj (Opposite.op n) :=
  (S.tensorHomEquiv (SSet.stdSimplex.obj n) X Y).trans SSet.yonedaEquiv

def tensorCosimplicialHomIso (X Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((tensorCosimplicialFamily S).obj X)).obj Y ≅ (X ⟶[SSet.{v}] Y) :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (simplexTensorHomEquiv S X Y n.unop)) (by
    intro n m f
    ext h
    change simplexTensorHomEquiv S X Y m.unop
      ((S.tensor.map (SSet.stdSimplex.map f.unop)).app X ≫ h) =
        (X ⟶[SSet.{v}] Y).map f (simplexTensorHomEquiv S X Y n.unop h)
    exact (congrArg SSet.yonedaEquiv
      (S.tensorHom_naturality_parameter (SSet.stdSimplex.map f.unop) X Y h)).trans
        (SSet.yonedaEquiv_naturality f.unop (S.tensorHomEquiv _ X Y h)).symm)

lemma tensorCosimplicialHomIso_source {X X' : C} (f : X ⟶ X') (Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((tensorCosimplicialFamily S).map f)).app Y ≫
        (tensorCosimplicialHomIso S X Y).hom =
      (tensorCosimplicialHomIso S X' Y).hom ≫ eHomWhiskerRight SSet.{v} f Y := by
  ext n h
  change simplexTensorHomEquiv S X Y n.unop
    ((S.tensor.obj (SSet.stdSimplex.obj n.unop)).map f ≫ h) =
    (eHomWhiskerRight SSet.{v} f Y).app n (simplexTensorHomEquiv S X' Y n.unop h)
  exact (congrArg SSet.yonedaEquiv
    (S.tensorHom_naturality_source (SSet.stdSimplex.obj n.unop) f Y h)).trans
      (SSet.yonedaEquiv_comp _ _)

lemma tensorCosimplicialHomIso_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((tensorCosimplicialFamily S).obj X)).map f ≫
        (tensorCosimplicialHomIso S X Y').hom =
      (tensorCosimplicialHomIso S X Y).hom ≫ eHomWhiskerLeft SSet.{v} X f := by
  ext n h
  change simplexTensorHomEquiv S X Y' n.unop (h ≫ f) =
    (eHomWhiskerLeft SSet.{v} X f).app n (simplexTensorHomEquiv S X Y n.unop h)
  exact (congrArg SSet.yonedaEquiv
    (S.tensorHom_naturality_target (SSet.stdSimplex.obj n.unop) X f h)).trans
      (SSet.yonedaEquiv_comp _ _)

def tensorHomBifunctorIso : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (tensorCosimplicialFamily S) (𝟭 C) ≅
    eHomFunctor SSet.{v} C :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (tensorCosimplicialHomIso S X.unop)
      (fun {_ _} f ↦ tensorCosimplicialHomIso_target S X.unop f))
    (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      exact tensorCosimplicialHomIso_source S f.unop Y)

abbrev enrichedReplacementHom (Q R : C ⥤ C) : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  Q.op ⋙ eHomFunctor SSet.{v} C ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj R

def replacedTensorHomIso (Q R : C ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (Q ⋙ tensorCosimplicialFamily S) R ≅ enrichedReplacementHom Q R :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ tensorCosimplicialHomIso S (Q.obj X.unop) (R.obj Y))
      (fun {_ _} f ↦ tensorCosimplicialHomIso_target S (Q.obj X.unop) (R.map f)))
    (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      exact tensorCosimplicialHomIso_source S (Q.map f.unop) (R.obj Y))

end SerrePositivity.HomotopyFunctionComplex
