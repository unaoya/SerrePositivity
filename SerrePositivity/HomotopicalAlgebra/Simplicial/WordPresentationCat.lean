module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationSourceMap

/-! # The presented word category as a functor of categories and simplicial word parameters -/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.WordPresentationCat

def functor (M : Type w) [MonoidWithZero M] : Cat.{v, u} ⥤ Cat.{max u v w, u} where
  obj C := Cat.of (RetractWords.Obj C M)
  map F := (RetractWords.map F.toFunctor (MonoidWithZeroHom.id M)).toCatHom
  map_id C := by
    apply Cat.Hom.ext
    exact RetractWords.map_id
  map_comp F G := by
    apply Cat.Hom.ext
    change RetractWords.map (F.toFunctor ⋙ G.toFunctor) (MonoidWithZeroHom.id M) =
      RetractWords.map F.toFunctor (MonoidWithZeroHom.id M) ⋙
        RetractWords.map G.toFunctor (MonoidWithZeroHom.id M)
    have h := RetractWords.map_comp F.toFunctor G.toFunctor
      (MonoidWithZeroHom.id M) (MonoidWithZeroHom.id M)
    simpa only [MonoidWithZeroHom.comp_id] using h

def changeParameters {M N : Type w} [MonoidWithZero M] [MonoidWithZero N]
    (h : M →*₀ N) : functor.{u, v} M ⟶ functor N where
  app C := (RetractWords.map (𝟭 C) h).toCatHom
  naturality {_ _} F := by
    apply Cat.Hom.ext
    change RetractWords.map F.toFunctor (MonoidWithZeroHom.id M) ⋙
        RetractWords.map (𝟭 _) h =
      RetractWords.map (𝟭 _) h ⋙ RetractWords.map F.toFunctor (MonoidWithZeroHom.id N)
    rw [← RetractWords.map_comp, ← RetractWords.map_comp]
    simp only [Functor.comp_id, Functor.id_comp, MonoidWithZeroHom.comp_id,
      MonoidWithZeroHom.id_comp]

lemma changeParameters_id (M : Type w) [MonoidWithZero M] :
    changeParameters.{u, v} (MonoidWithZeroHom.id M) = 𝟙 (functor M) := by
  apply NatTrans.ext
  funext C
  apply Cat.Hom.ext
  exact RetractWords.map_id

lemma changeParameters_comp {M N O : Type w} [MonoidWithZero M] [MonoidWithZero N]
    [MonoidWithZero O] (h : M →*₀ N) (k : N →*₀ O) :
    changeParameters.{u, v} (k.comp h) = changeParameters h ≫ changeParameters k := by
  apply NatTrans.ext
  funext C
  apply Cat.Hom.ext
  change RetractWords.map (𝟭 C) (k.comp h) = RetractWords.map (𝟭 C) h ⋙ RetractWords.map (𝟭 C) k
  rw [← RetractWords.map_comp, Functor.id_comp]

def simplicial : SimplicialObject (Cat.{v, u} ⥤ Cat.{max u v w, u}) where
  obj n := functor (WordSegment.degree.{w} n)
  map θ := changeParameters (WordSegment.degreeMap θ)
  map_id n := by rw [WordPresentationDiagram.degreeMap_id, changeParameters_id]
  map_comp f g := by rw [WordPresentationDiagram.degreeMap_comp, changeParameters_comp]

def simplicialFunctor : Cat.{v, u} ⥤ SimplicialObject Cat.{max u v w, u} := simplicial.flip

def bisimplicial (A : SimplicialObject Cat.{v, u}) :
    SimplicialObject (SimplicialObject Cat.{max u v w, u}) := A ⋙ simplicialFunctor

end SerrePositivity.SimplicialModel.WordPresentationCat
