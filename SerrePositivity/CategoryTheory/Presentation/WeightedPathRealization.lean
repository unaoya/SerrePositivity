module

public import SerrePositivity.CategoryTheory.Quiver.WeightedPathMaps
public import SerrePositivity.CategoryTheory.Presentation.AmbientWords

/-! # Evaluation of weighted paths in the actual ambient word quotient -/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverWeightedPaths
variable (V : Type u) [Quiver.{v} V] (M : Type w) [Monoid M]

abbrev target := AmbientWords.Obj (Paths V) M
abbrev targetSource := AmbientWords.sourceFunctor (Paths V) M
abbrev wordAt (X : V) (t : M) : (targetSource V M).obj X ⟶ (targetSource V M).obj X :=
  (AmbientWords.quotient (Paths V) M).map (AmbientWords.word (Paths V) M X t)

lemma wordAt_one (X : V) : wordAt V M X 1 = 𝟙 _ := AmbientWords.word_one (Paths V) M X

lemma wordAt_mul (X : V) (a t : M) :
    wordAt V M X (a * t) = wordAt V M X a ≫ wordAt V M X t :=
  AmbientWords.word_mul (Paths V) M X a t

def eval {X Y : V} : Path V M X Y → ((targetSource V M).obj X ⟶ (targetSource V M).obj Y)
  | .nil t => wordAt V M X t
  | .cons p e t => eval p ≫ (targetSource V M).map e.toPath ≫ wordAt V M Y t

lemma eval_mulLast {X Y : V} (p : Path V M X Y) (t : M) :
    eval V M (mulLast p t) = eval V M p ≫ wordAt V M Y t := by
  cases p with
  | nil a => exact AmbientWords.word_mul (Paths V) M X a t
  | cons p e a =>
    change _ ≫ _ ≫ wordAt V M _ (a * t) = _
    rw [wordAt_mul]
    simp only [eval, Category.assoc]

lemma eval_comp {X Y Z : V} (p : Path V M X Y) (q : Path V M Y Z) :
    eval V M (comp p q) = eval V M p ≫ eval V M q := by
  induction q with
  | nil t => exact eval_mulLast V M p t
  | cons q e t ih =>
    change eval V M (comp p q) ≫ _ ≫ _ = _
    rw [ih]
    simp only [eval, Category.assoc]

def encode : Obj V M ⥤ target V M where
  obj X := (targetSource V M).obj X
  map := eval V M
  map_id X := AmbientWords.word_one (Paths V) M X
  map_comp := eval_comp V M

def normalRealization : AmbientWords.Realization (Paths V) M (Obj V M) where
  ambient := sourceFunctor
  action _ t := .nil t
  action_one _ := rfl
  action_mul _ _ _ := rfl

def decode : target V M ⥤ Obj V M := (normalRealization V M).functor

lemma decode_source {X Y : V} (p : Quiver.Path X Y) :
    (decode V M).map ((targetSource V M).map p) =
      (sourceFunctor (V := V) (M := M)).map p :=
  (normalRealization V M).functor_source p

lemma decode_word (X : V) (t : M) : (decode V M).map (wordAt V M X t) = .nil t :=
  (normalRealization V M).functor_word X t

lemma decode_eval {X Y : V} (p : Path V M X Y) : (decode V M).map (eval V M p) = p := by
  induction p with
  | nil t => exact (normalRealization V M).functor_word X t
  | cons p e t ih =>
    change (decode V M).map (eval V M p ≫ (targetSource V M).map e.toPath ≫ wordAt V M _ t) = _
    rw [Functor.map_comp, Functor.map_comp, ih]
    rw [decode_source, decode_word]
    change comp p (comp ((Paths.lift (generators (V := V) (M := M))).map e.toPath) (.nil t)) = _
    rw [Paths.lift_toPath]
    change (mulLast p 1).cons e (1 * t) = p.cons e t
    rw [mulLast_one, one_mul]

lemma source_encode : sourceFunctor (V := V) (M := M) ⋙ encode V M = targetSource V M := by
  refine Paths.ext_functor (F := sourceFunctor ⋙ encode V M) (G := targetSource V M) rfl ?_
  intro X Y e
  change eval V M ((Paths.lift (generators (V := V) (M := M))).map e.toPath) = _
  rw [Paths.lift_toPath]
  change wordAt V M X 1 ≫ (targetSource V M).map e.toPath ≫ wordAt V M Y 1 = _
  rw [wordAt_one, wordAt_one]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

lemma decode_encode : decode V M ⋙ encode V M = 𝟭 (target V M) := by
  apply AmbientWords.functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change AmbientWords.Edge (Paths V) M X Y at e
    cases e with
    | source f =>
      have h := congr($(source_encode V M).map f)
      simp only [Functor.comp_map, decode, AmbientWords.Realization.functor_source]
      exact heq_of_eq h
    | word X t =>
      simp only [Functor.comp_map, decode, AmbientWords.Realization.functor_word]
      rfl

def normalFormEquiv (X Y : V) : Path V M X Y ≃
    ((targetSource V M).obj X ⟶ (targetSource V M).obj Y) where
  toFun := eval V M
  invFun := (decode V M).map
  left_inv := decode_eval V M
  right_inv f := congr($(decode_encode V M).map f)

end SerrePositivity.QuiverWeightedPaths
