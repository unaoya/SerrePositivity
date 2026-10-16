module

public import SerrePositivity.CategoryTheory.Presentation.AmbientWordComparison
public import SerrePositivity.CategoryTheory.Presentation.RetractWordMap

/-! # The ambient comparison commutes with source and word parameter maps -/

@[expose] public section
universe u v w u' v' w'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AmbientWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {D : Type u'} [Category.{v'} D] {N : Type w'} [MonoidWithZero N]

def mapRealization (F : C ⥤ D) (h : M →*₀ N) : Realization C M (Obj D N) where
  ambient := F ⋙ sourceFunctor D N
  action X t := loop D N (F.obj X) (h t)
  action_one X := by
    change loop D N (F.obj X) (h 1) = 𝟙 _
    rw [map_one]
    exact word_one D N (F.obj X)
  action_mul X t z := by
    change loop D N (F.obj X) (h (t * z)) = _
    rw [map_mul]
    exact word_mul D N (F.obj X) (h t) (h z)

def map (F : C ⥤ D) (h : M →*₀ N) : Obj C M ⥤ Obj D N := (mapRealization F h).functor

lemma map_source (F : C ⥤ D) (h : M →*₀ N) {X Y : C} (f : X ⟶ Y) :
    (map F h).map ((quotient C M).map (source C M f)) =
      (quotient D N).map (source D N (F.map f)) :=
  (mapRealization F h).functor_source f

lemma map_loop (F : C ⥤ D) (h : M →*₀ N) (X : C) (t : M) :
    (map F h).map (loop C M X t) = loop D N (F.obj X) (h t) :=
  (mapRealization F h).functor_word X t

lemma map_toRetract (F : C ⥤ D) (h : M →*₀ N) :
    map F h ⋙ toRetract D N = toRetract C M ⋙ RetractWords.map F h := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f =>
      simp only [Functor.comp_map, map_source, toRetract_source, RetractWords.map_source]
      rfl
    | word X t =>
      simp only [Functor.comp_map, map_loop, toRetract_loop, RetractWords.map_word]
      rfl

end SerrePositivity.AmbientWords
