module

public import SerrePositivity.CategoryTheory.Presentation.WeightedPathRealization
public import SerrePositivity.CategoryTheory.Presentation.AmbientWordMap
public import SerrePositivity.CategoryTheory.Presentation.AmbientWordAugmentation

/-! # Normal forms preserve the actual word-parameter maps and augmentation -/

@[expose] public section
universe u v w w'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverWeightedPaths
variable (V : Type u) [Quiver.{v} V]

section Augmentation
variable (M : Type w) [Monoid M]

lemma augmentation_eval {X Y : V} (p : Path V M X Y) :
    (AmbientWords.augmentation (Paths V) M).map (eval V M p) = forget p := by
  induction p with
  | nil t => exact AmbientWords.augmentation_word (Paths V) M X t
  | @cons Y Z p e t ih =>
    change (AmbientWords.augmentation (Paths V) M).map
      (eval V M p ≫ (targetSource V M).map e.toPath ≫ wordAt V M _ t) = _
    rw [Functor.map_comp, Functor.map_comp, ih]
    have hs : (AmbientWords.augmentation (Paths V) M).map
        ((targetSource V M).map e.toPath) = e.toPath :=
      AmbientWords.augmentation_source (Paths V) M e.toPath
    rw [hs]
    have ht : (AmbientWords.augmentation (Paths V) M).map (wordAt V M Z t) =
        𝟙 (show Paths V from Z) :=
      AmbientWords.augmentation_word (Paths V) M Z t
    rw [ht]
    rfl

end Augmentation

variable {M : Type w} [MonoidWithZero M] {N : Type w'} [MonoidWithZero N]

lemma parameter_word (h : M →*₀ N) (X : V) (t : M) :
    (AmbientWords.map (𝟭 (Paths V)) h).map (wordAt V M X t) = wordAt V N X (h t) :=
  AmbientWords.map_loop (𝟭 (Paths V)) h X t

lemma parameter_source (h : M →*₀ N) {X Y : V} (p : Quiver.Path X Y) :
    (AmbientWords.map (𝟭 (Paths V)) h).map ((targetSource V M).map p) =
      (targetSource V N).map p := AmbientWords.map_source (𝟭 (Paths V)) h p

lemma map_eval (h : M →*₀ N) {X Y : V} (p : Path V M X Y) :
    (AmbientWords.map (𝟭 (Paths V)) h).map (eval V M p) = eval V N (mapWeights h p) := by
  induction p with
  | nil t => exact parameter_word V h X t
  | cons p e t ih =>
    change (AmbientWords.map (𝟭 (Paths V)) h).map
      (eval V M p ≫ (targetSource V M).map e.toPath ≫ wordAt V M _ t) = _
    rw [Functor.map_comp, Functor.map_comp, ih, parameter_source, parameter_word]
    rfl

end SerrePositivity.QuiverWeightedPaths
