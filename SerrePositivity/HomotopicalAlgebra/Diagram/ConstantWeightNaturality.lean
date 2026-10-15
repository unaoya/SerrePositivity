module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightRealization

/-! # Naturality of constant-weight realization in source frames -/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.ConstantWeightRealization
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w, w} C]

abbrev degreeMap {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) (n : SimplexCategory) :
    ConstantWeightHom.degree K A n ⟶ ConstantWeightHom.degree K B n :=
  Functor.whiskerRight a ((evaluation SimplexCategory C).obj n)

omit [HasColimitsOfSize.{w, w} C] in
lemma weightHomEquiv_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (n : SimplexCategory) (Y : C)
    (t : ConstantWeightHom.weight K n ⟶ (FrameWeightRealization.hom K B).obj Y) :
    ConstantWeightHom.homEquiv K A n Y
        (t ≫ ((FrameWeightRealization.homFamily K).map a.op).app Y) =
      degreeMap K a n ≫ ConstantWeightHom.homEquiv K B n Y t := by
  rfl

lemma homEquiv_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (n : SimplexCategory) (Y : C)
    (t : (FrameWeightRealization.functor K B).obj (ConstantWeightHom.weight K n) ⟶ Y) :
    homEquiv K A n Y ((FrameWeightRealization.map K a).app _ ≫ t) =
      colim.map (degreeMap K a n) ≫ homEquiv K B n Y t := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [FrameWeightRealization.homEquiv_frame_naturality, weightHomEquiv_frame_naturality]
  exact (colimConstAdj (J := K) (C := C)).homEquiv_naturality_left_symm _ _

lemma iso_inv_comp (A : K ⥤ SimplexCategory ⥤ C) (n : SimplexCategory) (Y : C)
    (t : (FrameWeightRealization.functor K A).obj (ConstantWeightHom.weight K n) ⟶ Y) :
    (iso K A n).inv ≫ t = homEquiv K A n Y t := by
  have h := Coyoneda.fullyFaithful.map_preimage (coyonedaIso K A n).hom
  exact congrArg (fun z => z.app Y t) h

@[reassoc]
lemma iso_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (n : SimplexCategory) :
    (FrameWeightRealization.map K a).app (ConstantWeightHom.weight K n) ≫ (iso K B n).hom =
      (iso K A n).hom ≫ colim.map (degreeMap K a n) := by
  apply (homEquiv K A n _).injective
  rw [homEquiv_frame_naturality, homEquiv_target_naturality,
    ← iso_inv_comp, ← iso_inv_comp]
  simp

@[reassoc]
lemma unitIso_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) :
    (FrameWeightRealization.map K a).app (unitWeight K) ≫ (unitIso K B).hom =
      (unitIso K A).hom ≫ colim.map (degreeMap K a (SimplexCategory.mk 0)) := by
  change (FrameWeightRealization.map K a).app (unitWeight K) ≫
    ((FrameWeightRealization.functor K B).map _ ≫ _) =
      ((FrameWeightRealization.functor K A).map _ ≫ _) ≫ _
  rw [← Category.assoc, ← (FrameWeightRealization.map K a).naturality,
    Category.assoc, iso_frame_naturality, ← Category.assoc]

end SerrePositivity.DiagramModel.ConstantWeightRealization
