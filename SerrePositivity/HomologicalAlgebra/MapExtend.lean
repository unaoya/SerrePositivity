module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-! # Additive functors commute with extension by zero -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {E : Type u'} [Category.{v'} E] [Preadditive E] [HasZeroObject E]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (F : C ⥤ E) [F.Additive] (K : HomologicalComplex C c) (e : c.Embedding c')

/-- Compare a degree of extension by zero before and after applying an additive functor. -/
def mapExtendXIso (i : ι') :
    ((F.mapHomologicalComplex c').obj (K.extend e)).X i ≅
      (((F.mapHomologicalComplex c).obj K).extend e).X i := by
  classical
  exact if h : ∃ j, e.f j = i then
    F.mapIso (K.extendXIso e h.choose_spec) ≪≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec).symm
  else (F.map_isZero (K.isZero_extend_X e i (fun j hj => h ⟨j, hj⟩))).iso
    (((F.mapHomologicalComplex c).obj K).isZero_extend_X e i (fun j hj => h ⟨j, hj⟩))

/-- The cochain comparison respects differentials, including the zero degrees. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (mapExtendXIso F K e) ?_
  intro i j _
  by_cases hi : ∃ a, e.f a = i
  · by_cases hj : ∃ b, e.f b = j
    · simp only [mapExtendXIso, dite_eq_left hi, dite_eq_left hj, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom]
      change (F.map (K.extendXIso e hi.choose_spec).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e hi.choose_spec).inv) ≫ _ =
        F.map ((K.extend e).d i j) ≫ _
      rw [extend_d_eq _ e hi.choose_spec hj.choose_spec,
        extend_d_eq K e hi.choose_spec hj.choose_spec]
      simp [Functor.map_comp, Category.assoc]
    · exact (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j
        (fun b hb => hj ⟨b, hb⟩)).eq_of_tgt _ _
  · exact (F.map_isZero (K.isZero_extend_X e i (fun a ha => hi ⟨a, ha⟩))).eq_of_src _ _

/-- Extension by zero commutes with additive functors naturally in the complex. -/
lemma mapExtendIso_naturality {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e) ≫
        (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map f) e := by
  classical
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : ∃ a, e.f a = i
  · change F.map ((HomologicalComplex.extendMap f e).f i) ≫ (mapExtendXIso F L e i).hom =
      (mapExtendXIso F K e i).hom ≫ _
    simp only [mapExtendXIso, dite_eq_left hi, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [extendMap_f _ e hi.choose_spec, extendMap_f _ e hi.choose_spec]
    simp [Functor.map_comp, Category.assoc]
  · exact (F.map_isZero (K.isZero_extend_X e i (fun a ha => hi ⟨a, ha⟩))).eq_of_src _ _

/-- The extension comparison is natural in the additive functor as well. -/
lemma mapExtendIso_natTrans {G : C ⥤ E} [G.Additive] (α : F ⟶ G) :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫ (mapExtendIso G K e).hom =
      (mapExtendIso F K e).hom ≫ HomologicalComplex.extendMap
        ((NatTrans.mapHomologicalComplex α c).app K) e := by
  classical
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : ∃ a, e.f a = i
  · change α.app ((K.extend e).X i) ≫ (mapExtendXIso G K e i).hom =
      (mapExtendXIso F K e i).hom ≫ _
    simp only [mapExtendXIso, dite_eq_left hi, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [extendMap_f _ e hi.choose_spec]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← α.naturality]
    simp only [Category.assoc]
    rfl
  · exact (F.map_isZero (K.isZero_extend_X e i (fun a ha => hi ⟨a, ha⟩))).eq_of_src _ _

end SerrePositivity
