module

public import Mathlib.CategoryTheory.Shift.CommShift

/-! # 完全忠実な前合成に沿ったシフト両立性の延長 -/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor

variable {M : Type*} [AddMonoid M] {B C D : Type*} [Category* B] [Category* C] [Category* D]
  [HasShift B M] [HasShift C M] [HasShift D M]
  (L : B ⥤ C) (F : C ⥤ D) (H : B ⥤ D) (e : L ⋙ F ≅ H)
  [L.CommShift M] [H.CommShift M]
  [((whiskeringLeft B C D).obj L).Full] [((whiskeringLeft B C D).obj L).Faithful]

/-- 前合成後のシフト同型から構成するシフト同型。 -/
noncomputable def precompShiftIso (n : M) : shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n :=
  ((whiskeringLeft B C D).obj L).preimageIso
    (isoWhiskerRight (L.commShiftIso n).symm F ≪≫
      isoWhiskerLeft (shiftFunctor B n) e ≪≫ H.commShiftIso n ≪≫
      isoWhiskerRight e.symm (shiftFunctor D n))

@[simp, reassoc] lemma precompShiftIso_hom_app (n : M) (X : B) :
    (precompShiftIso L F H e n).hom.app (L.obj X) =
      F.map ((L.commShiftIso n).inv.app X) ≫ e.hom.app (X⟦n⟧) ≫
        (H.commShiftIso n).hom.app X ≫ (e.inv.app X)⟦n⟧' := by
  have h : ((whiskeringLeft B C D).obj L).map (precompShiftIso L F H e n).hom =
    (isoWhiskerRight (L.commShiftIso n).symm F ≪≫
      isoWhiskerLeft (shiftFunctor B n) e ≪≫ H.commShiftIso n ≪≫
      isoWhiskerRight e.symm (shiftFunctor D n)).hom := Functor.map_preimage _ _
  exact congr_app h X

attribute [irreducible] precompShiftIso

/-- 関手圏での前合成が完全忠実なら、シフトとの両立を延長できる。 -/
@[instance_reducible] noncomputable def commShiftOfPrecomp : F.CommShift M where
  commShiftIso := precompShiftIso L F H e
  commShiftIso_zero := by
    apply Iso.ext
    apply ((whiskeringLeft B C D).obj L).map_injective
    ext X
    change (precompShiftIso L F H e 0).hom.app (L.obj X) =
      (CommShift.isoZero F M).hom.app (L.obj X)
    simp only [precompShiftIso_hom_app, L.commShiftIso_zero, H.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.CommShift.isoZero_inv_app,
      Functor.map_comp, Category.assoc]
    have hn := e.hom.naturality ((shiftFunctorZero B M).inv.app X)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← H.map_comp_assoc, Iso.inv_hom_id_app]
    rw [← (shiftFunctorZero D M).inv.naturality]
    simp
  commShiftIso_add a b := by
    apply Iso.ext
    apply ((whiskeringLeft B C D).obj L).map_injective
    ext X
    change (precompShiftIso L F H e (a + b)).hom.app (L.obj X) =
      (CommShift.isoAdd (precompShiftIso L F H e a)
        (precompShiftIso L F H e b)).hom.app (L.obj X)
    simp only [precompShiftIso_hom_app, L.commShiftIso_add, H.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_inv_app,
      Functor.map_comp, Category.assoc]
    have hn := e.hom.naturality ((shiftFunctorAdd B a b).inv.app X)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← H.map_comp_assoc, Iso.inv_hom_id_app]
    rw [← (shiftFunctorAdd D a b).inv.naturality]
    simp only [Functor.comp_map]
    have hn' := (precompShiftIso L F H e b).hom.naturality
      ((L.commShiftIso a).inv.app X)
    dsimp only [Functor.comp_map] at hn'
    rw [← reassoc_of% hn', precompShiftIso_hom_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp

/-- 構成したシフト両立性では、元の比較同型もシフトと両立する。 -/
lemma commShiftOfPrecomp_compatibility :
    letI := commShiftOfPrecomp (M := M) L F H e
    NatTrans.CommShift e.hom M := by
  let := commShiftOfPrecomp (M := M) L F H e
  refine ⟨fun n ↦ ?_⟩
  ext X
  simp [Functor.commShiftIso_comp_hom_app,
    show F.commShiftIso n = precompShiftIso L F H e n from rfl]

end SerrePositivity
