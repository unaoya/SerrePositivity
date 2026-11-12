module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.Spectra.General.Evaluation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! # Level morphism classes and free-level generators

The generating classes use the left adjoints F_n, and their right lifting
classes are proved to be exactly the levelwise classes. These computations do
not assume a model structure on spectra or an acyclicity condition.
-/

@[expose] public section
universe w u v
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.ModelGeneration

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (K : C)

/-- A property holds at every level of the underlying symmetric sequence. -/
def levelProperty (P : MorphismProperty C) : MorphismProperty (GeneralSymmetricSpectrum C K) :=
  fun _ _ f ↦ ∀ n : ℕ, P (levelMap f n)

/-- All free-level images of a generating class, as strict images for the SOA. -/
def levelGenerators (P : MorphismProperty C) : MorphismProperty (GeneralSymmetricSpectrum C K) :=
  ⨆ n : ℕ, P.strictMap (freeAt (K := K) n)

lemma levelProperty_inf (P Q : MorphismProperty C) :
    levelProperty K (P ⊓ Q) = levelProperty K P ⊓ levelProperty K Q := by
  ext A B f
  constructor
  · intro h
    exact ⟨fun n ↦ (h n).1, fun n ↦ (h n).2⟩
  · rintro ⟨hP, hQ⟩ n
    exact ⟨hP n, hQ n⟩

/-- The free/evaluation adjunction computes all right lifting conditions. -/
lemma levelGenerators_rlp (P : MorphismProperty C) :
    (levelGenerators K P).rlp = levelProperty K P.rlp := by
  ext A B f
  constructor
  · intro h n X Y i hi
    exact ((freeAtAdjunction (K := K) n).hasLiftingProperty_iff i f).1
      (h _ ((le_iSup (fun n : ℕ ↦ P.strictMap (freeAt (K := K) n)) n) _
        (P.map_mem_strictMap _ i hi)))
  · intro h X Y i hi
    change (⨆ n : ℕ, P.strictMap (freeAt (K := K) n)) i at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, hi⟩ := hi
    cases hi with
    | map hi =>
      exact ((freeAtAdjunction (K := K) n).hasLiftingProperty_iff _ f).2 (h n _ hi)

variable [ModelCategory C] (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I J in
lemma generatingCofibrations_rlp :
    (levelGenerators K I).rlp = levelProperty K (trivialFibrations C) := by
  rw [levelGenerators_rlp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)]

include I J in
lemma generatingTrivialCofibrations_rlp :
    (levelGenerators K J).rlp = levelProperty K (fibrations C) := by
  rw [levelGenerators_rlp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J (I := I) (J := J)]
end SerrePositivity.SpectrumLevelModel
