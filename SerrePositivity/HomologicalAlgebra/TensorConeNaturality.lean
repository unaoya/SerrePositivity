module
public import SerrePositivity.PerfectComplex.TensorCone
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality
public import SerrePositivity.HomologicalAlgebra.CochainConeNaturality

/-! # Naturality of tensoring a mapping cone in the remaining tensor variable -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {R : Type u} [CommRing R]
variable {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q')

/-- Tensor-cone first coordinates respect a change in the other tensor factor. -/
lemma tensorConeFstX_naturality_right (n : ℤ) :
    (cochainTensorMap (𝟙 (mappingCone f)) g).f n ≫ tensorConeFstX f Q' n =
      tensorConeFstX f Q n ≫ (cochainTensorMap (𝟙 P) g).f (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [cochainTensorMap_homogeneous_assoc, ι_tensorConeFstX, ι_tensorConeFstX_assoc,
    cochainTensorMap_homogeneous]
  simp only [HomologicalComplex.id_f, id_tensorHom]
  rw [← whisker_exchange_assoc]

/-- Tensor-cone second coordinates respect a change in the other tensor factor. -/
lemma tensorConeSndX_naturality_right (n : ℤ) :
    (cochainTensorMap (𝟙 (mappingCone f)) g).f n ≫ tensorConeSndX f Q' n =
      tensorConeSndX f Q n ≫ (cochainTensorMap (𝟙 P') g).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [cochainTensorMap_homogeneous_assoc, ι_tensorConeSndX, ι_tensorConeSndX_assoc,
    cochainTensorMap_homogeneous]
  simp only [HomologicalComplex.id_f, id_tensorHom]
  rw [← whisker_exchange_assoc]

/-- The arrow map induced by a change of the remaining tensor variable. -/
def tensorConeRightArrowMap :
    Arrow.mk (cochainTensorMap f (𝟙 Q)) ⟶ Arrow.mk (cochainTensorMap f (𝟙 Q')) :=
  Arrow.homMk (cochainTensorMap (𝟙 P) g) (cochainTensorMap (𝟙 P') g) (by
    change cochainTensorMap (𝟙 P) g ≫ cochainTensorMap f (𝟙 Q') =
      cochainTensorMap f (𝟙 Q) ≫ cochainTensorMap (𝟙 P') g
    rw [cochainTensorMap_comp, cochainTensorMap_comp]
    simp only [Category.comp_id, Category.id_comp])

/-- The tensor-cone comparison is natural in the remaining tensor complex. -/
lemma cochainTensorConeLeft_naturality_right :
    cochainTensorMap (𝟙 (mappingCone f)) g ≫ (cochainTensorConeLeft f Q').hom =
      (cochainTensorConeLeft f Q).hom ≫ homotopyCofiber.mapArrowHom
        (cochainTensorMap f (𝟙 Q)) (cochainTensorMap f (𝟙 Q'))
        (fun j => ⟨j - 1, by simp⟩) (tensorConeRightArrowMap f g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_to (cochainTensorMap f (𝟙 Q')) n (n + 1) rfl
  · have hp : (homotopyCofiber.mapArrowHom
        (cochainTensorMap f (𝟙 Q)) (cochainTensorMap f (𝟙 Q'))
        (fun j => ⟨j - 1, by simp⟩) (tensorConeRightArrowMap f g)).f n ≫
          (mappingCone.fst (cochainTensorMap f (𝟙 Q'))).1.v n (n + 1) rfl =
        (mappingCone.fst (cochainTensorMap f (𝟙 Q))).1.v n (n + 1) rfl ≫
          (cochainTensorMap (𝟙 P) g).f (n + 1) :=
      DerivedCompletion.moduleConeArrowMap_fst _ _ (tensorConeRightArrowMap f g) n (n + 1) rfl
    change ((cochainTensorMap (𝟙 (mappingCone f)) g).f n ≫
        (tensorConeXIso f Q' n).hom) ≫ _ = ((tensorConeXIso f Q n).hom ≫ _) ≫ _
    simp only [Category.assoc, tensorConeXIso_hom_fst,
      hp]
    rw [← Category.assoc, tensorConeXIso_hom_fst]
    exact tensorConeFstX_naturality_right f g n
  · have hp : (homotopyCofiber.mapArrowHom
        (cochainTensorMap f (𝟙 Q)) (cochainTensorMap f (𝟙 Q'))
        (fun j => ⟨j - 1, by simp⟩) (tensorConeRightArrowMap f g)).f n ≫
          (mappingCone.snd (cochainTensorMap f (𝟙 Q'))).v n n (add_zero n) =
        (mappingCone.snd (cochainTensorMap f (𝟙 Q))).v n n (add_zero n) ≫
          (cochainTensorMap (𝟙 P') g).f n :=
      DerivedCompletion.moduleConeArrowMap_snd _ _ (tensorConeRightArrowMap f g) n
    change ((cochainTensorMap (𝟙 (mappingCone f)) g).f n ≫
        (tensorConeXIso f Q' n).hom) ≫ _ = ((tensorConeXIso f Q n).hom ≫ _) ≫ _
    simp only [Category.assoc, tensorConeXIso_hom_snd,
      hp]
    rw [← Category.assoc, tensorConeXIso_hom_snd]
    exact tensorConeSndX_naturality_right f g n

end SerrePositivity
