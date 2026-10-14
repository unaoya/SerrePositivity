module

public import SerrePositivity.PerfectComplex.TensorDegreeMaps

/-! # Tensoring degreewise split short exact sequences of complexes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

/-- A degreewise retraction with explicit component types. -/
abbrev cochainSplittingRetraction
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ) : S.X₂.X i ⟶ S.X₁.X i := (σ i).r

/-- A degreewise section with explicit component types. -/
abbrev cochainSplittingSection
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ) : S.X₃.X i ⟶ S.X₂.X i := (σ i).s

/-- Tensor a short complex on the right by a fixed cochain complex. -/
abbrev cochainTensorShortComplexRight
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) := S.map (cochainTensorFixedRight Q)

/-- A degreewise splitting induces a degreewise splitting after total tensoring. -/
def cochainTensorShortComplexRightSplitting
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((cochainTensorShortComplexRight S Q).map (eval _ _ n)).Splitting where
  r := cochainTensorDegreeMap (cochainSplittingRetraction S σ) (fun j => 𝟙 (Q.X j)) n
  s := cochainTensorDegreeMap (cochainSplittingSection S σ) (fun j => 𝟙 (Q.X j)) n
  f_r := by
    change (cochainTensorMap S.f (𝟙 Q)).f n ≫ _ = 𝟙 ((cochainTensor S.X₁ Q).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
    have h : (fun i => S.f.f i ≫ cochainSplittingRetraction S σ i) = (fun i => 𝟙 (S.X₁.X i)) :=
      funext fun i => (σ i).f_r
    rw [h, cochainTensorDegreeMap_id]
  s_g := by
    change _ ≫ (cochainTensorMap S.g (𝟙 Q)).f n = 𝟙 ((cochainTensor S.X₃ Q).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    have h : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) = (fun i => 𝟙 (S.X₃.X i)) :=
      funext fun i => (σ i).s_g
    rw [h, cochainTensorDegreeMap_id]
  id := by
    change cochainTensorDegreeMap (cochainSplittingRetraction S σ) (fun j => 𝟙 (Q.X j)) n ≫
      (cochainTensorMap S.f (𝟙 Q)).f n + (cochainTensorMap S.g (𝟙 Q)).f n ≫
      cochainTensorDegreeMap (cochainSplittingSection S σ) (fun j => 𝟙 (Q.X j)) n =
      𝟙 ((cochainTensor S.X₂ Q).X n)
    rw [← cochainTensorDegreeMap_eq, ← cochainTensorDegreeMap_eq,
      cochainTensorDegreeMap_comp, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    rw [← cochainTensorDegreeMap_add_left]
    have h : (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i +
        S.g.f i ≫ cochainSplittingSection S σ i) =
        (fun i => 𝟙 (S.X₂.X i)) := funext fun i => (σ i).id
    rw [h, cochainTensorDegreeMap_id]

lemma cochainTensorShortComplexRight_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorShortComplexRight S Q).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (cochainTensorShortComplexRightSplitting S σ Q n).shortExact)

/-- Tensor a short complex on the left by a fixed cochain complex. -/
abbrev cochainTensorShortComplexLeft
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) := S.map (cochainTensorFixedLeft P)

/-- The corresponding degreewise splitting for left tensoring. -/
def cochainTensorShortComplexLeftSplitting
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (n : ℤ) :
    ((cochainTensorShortComplexLeft P S).map (eval _ _ n)).Splitting where
  r := cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingRetraction S σ) n
  s := cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingSection S σ) n
  f_r := by
    change (cochainTensorMap (𝟙 P) S.f).f n ≫ _ = 𝟙 ((cochainTensor P S.X₁).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
    have h : (fun j => S.f.f j ≫ cochainSplittingRetraction S σ j) = (fun j => 𝟙 (S.X₁.X j)) :=
      funext fun j => (σ j).f_r
    rw [h, cochainTensorDegreeMap_id]
  s_g := by
    change _ ≫ (cochainTensorMap (𝟙 P) S.g).f n = 𝟙 ((cochainTensor P S.X₃).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    have h : (fun j => cochainSplittingSection S σ j ≫ S.g.f j) = (fun j => 𝟙 (S.X₃.X j)) :=
      funext fun j => (σ j).s_g
    rw [h, cochainTensorDegreeMap_id]
  id := by
    change cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingRetraction S σ) n ≫
      (cochainTensorMap (𝟙 P) S.f).f n + (cochainTensorMap (𝟙 P) S.g).f n ≫
      cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingSection S σ) n =
      𝟙 ((cochainTensor P S.X₂).X n)
    rw [← cochainTensorDegreeMap_eq, ← cochainTensorDegreeMap_eq,
      cochainTensorDegreeMap_comp, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    rw [← cochainTensorDegreeMap_add_right]
    have h : (fun j => cochainSplittingRetraction S σ j ≫ S.f.f j +
        S.g.f j ≫ cochainSplittingSection S σ j) =
        (fun j => 𝟙 (S.X₂.X j)) := funext fun j => (σ j).id
    rw [h, cochainTensorDegreeMap_id]

lemma cochainTensorShortComplexLeft_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (cochainTensorShortComplexLeft P S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (cochainTensorShortComplexLeftSplitting P S σ n).shortExact)

/-- Short exact sequences with projective quotient terms split in every degree. -/
def cochainDegreewiseSplittingOfProjective
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) (i : ℤ) :
    (S.map (eval _ _ i)).Splitting := by
  have := hS.mono_f
  have := hS.epi_g
  have := hproj i
  letI : Projective ((S.map (eval _ _ i)).X₃) := by
    change Projective (S.X₃.X i)
    infer_instance
  exact (hS.map (eval _ _ i)).splittingOfProjective

lemma cochainTensorShortComplexRight_shortExact_of_projective
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i))
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorShortComplexRight S Q).ShortExact :=
  cochainTensorShortComplexRight_shortExact S (cochainDegreewiseSplittingOfProjective S hS hproj) Q

lemma cochainTensorShortComplexLeft_shortExact_of_projective
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    (cochainTensorShortComplexLeft P S).ShortExact :=
  cochainTensorShortComplexLeft_shortExact P S (cochainDegreewiseSplittingOfProjective S hS hproj)

end SerrePositivity
