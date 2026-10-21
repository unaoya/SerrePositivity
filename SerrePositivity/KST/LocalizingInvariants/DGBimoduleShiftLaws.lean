module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftActions
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftCrossNaturality
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftAssociatorLeft
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftAssociatorMiddle
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftUnitors

/-!
概要：符号付き shift 作用に対する単位則・結合則・左右作用の交換則。
方針：tensor–shift の自然性・associator・unitor 比較で元の双加群三則を移す。
規約：三則を仮定入力にしない。使われ方：実 dg 双加群の shift。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} (M : Bimod A A) (s : ℤ)

lemma one_actLeft : (η[A.X] ▷ M.X⟦s⟧) ≫ actLeft M s = (λ_ (M.X⟦s⟧)).hom := by
  unfold actLeft
  rw [← Category.assoc, tensorShiftRight_naturality_left, Category.assoc,
    ← Functor.map_comp, M.one_actLeft]
  exact tensorShift_leftUnitor M.X s

lemma actRight_one : (M.X⟦s⟧ ◁ η[A.X]) ≫ actRight M s = (ρ_ (M.X⟦s⟧)).hom := by
  unfold actRight
  rw [← Category.assoc, tensorShiftLeft_naturality_right, Category.assoc,
    ← Functor.map_comp, M.actRight_one]
  exact tensorShift_rightUnitor M.X s

lemma left_assoc : (μ[A.X] ▷ M.X⟦s⟧) ≫ actLeft M s =
    (α_ A.X A.X (M.X⟦s⟧)).hom ≫ (A.X ◁ actLeft M s) ≫ actLeft M s := by
  have hn := cochainTensorShiftRight_naturality (P := A.X) M.actLeft s
  change (A.X ◁ M.actLeft⟦s⟧') ≫ (cochainTensorShiftRight A.X M.X s).hom =
    (cochainTensorShiftRight A.X (A.X ⊗ M.X) s).hom ≫ (A.X ◁ M.actLeft)⟦s⟧' at hn
  simp only [actLeft, whiskerLeft_comp, Category.assoc]
  rw [tensorShiftRight_naturality_left_assoc, ← Functor.map_comp, M.left_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hc : (α_ A.X A.X (M.X⟦s⟧)).hom ≫
      (A.X ◁ (cochainTensorShiftRight A.X M.X s).hom) ≫
        (cochainTensorShiftRight A.X (A.X ⊗ M.X) s).hom =
      (cochainTensorShiftRight (A.X ⊗ A.X) M.X s).hom ≫
        (α_ A.X A.X M.X).hom⟦s⟧' := tensorShift_associator_right A.X A.X M.X s
  rw [reassoc_of% hn, reassoc_of% hc]

lemma right_assoc_hom : (actRight M s ▷ A.X) ≫ actRight M s =
    (α_ (M.X⟦s⟧) A.X A.X).hom ≫ (M.X⟦s⟧ ◁ μ[A.X]) ≫ actRight M s := by
  have hn := cochainTensorShiftLeft_naturality (Q := A.X) M.actRight s
  change (M.actRight⟦s⟧' ▷ A.X) ≫ (cochainTensorShiftLeft M.X A.X s).hom =
    (cochainTensorShiftLeft (M.X ⊗ A.X) A.X s).hom ≫ (M.actRight ▷ A.X)⟦s⟧' at hn
  have hm : (M.actRight ▷ A.X) ≫ M.actRight =
      (α_ M.X A.X A.X).hom ≫ (M.X ◁ μ[A.X]) ≫ M.actRight := by
    rw [M.right_assoc, Iso.hom_inv_id_assoc]
  simp only [actRight, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, hm]
  simp only [Functor.map_comp, Category.assoc]
  have hc : (α_ (M.X⟦s⟧) A.X A.X).hom ≫
      (cochainTensorShiftLeft M.X (A.X ⊗ A.X) s).hom =
      ((cochainTensorShiftLeft M.X A.X s).hom ▷ A.X) ≫
        (cochainTensorShiftLeft (M.X ⊗ A.X) A.X s).hom ≫
          (α_ M.X A.X A.X).hom⟦s⟧' := tensorShift_associator_left M.X A.X A.X s
  rw [← reassoc_of% hc, ← tensorShiftLeft_naturality_right_assoc]

lemma right_assoc : (M.X⟦s⟧ ◁ μ[A.X]) ≫ actRight M s =
    (α_ (M.X⟦s⟧) A.X A.X).inv ≫ (actRight M s ▷ A.X) ≫ actRight M s := by
  apply (cancel_epi (α_ (M.X⟦s⟧) A.X A.X).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using (right_assoc_hom M s).symm

lemma middle_assoc : (actLeft M s ▷ A.X) ≫ actRight M s =
    (α_ A.X (M.X⟦s⟧) A.X).hom ≫ (A.X ◁ actRight M s) ≫ actLeft M s := by
  have hn := cochainTensorShiftLeft_naturality (Q := A.X) M.actLeft s
  change (M.actLeft⟦s⟧' ▷ A.X) ≫ (cochainTensorShiftLeft M.X A.X s).hom =
    (cochainTensorShiftLeft (A.X ⊗ M.X) A.X s).hom ≫ (M.actLeft ▷ A.X)⟦s⟧' at hn
  have hr := cochainTensorShiftRight_naturality (P := A.X) M.actRight s
  change (A.X ◁ M.actRight⟦s⟧') ≫ (cochainTensorShiftRight A.X M.X s).hom =
    (cochainTensorShiftRight A.X (M.X ⊗ A.X) s).hom ≫ (A.X ◁ M.actRight)⟦s⟧' at hr
  simp only [actLeft, actRight, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, M.middle_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hc : (α_ A.X (M.X⟦s⟧) A.X).hom ≫
      (A.X ◁ (cochainTensorShiftLeft M.X A.X s).hom) ≫
        (cochainTensorShiftRight A.X (M.X ⊗ A.X) s).hom =
      ((cochainTensorShiftRight A.X M.X s).hom ▷ A.X) ≫
        (cochainTensorShiftLeft (A.X ⊗ M.X) A.X s).hom ≫
          (α_ A.X M.X A.X).hom⟦s⟧' := tensorShift_associator_middle A.X M.X A.X s
  rw [← reassoc_of% hc, ← reassoc_of% hr]

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
