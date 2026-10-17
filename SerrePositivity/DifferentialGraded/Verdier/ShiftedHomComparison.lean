module
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-! # 関手の Hom 写像の全単射性の同型・整数 shift による移送 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T] (F : C ⥤ T)

lemma homComparison_bijective_of_iso {X Y X' Y' : C} (e : X ≅ X') (d : Y ≅ Y')
    (h : Function.Bijective (F.map (X := X) (Y := Y))) :
    Function.Bijective (F.map (X := X') (Y := Y')) := by
  have hc : Function.Bijective (fun f : X ⟶ Y => F.map (Iso.homCongr e d f)) := by
    simpa only [Functor.map_homCongr, Function.comp_def] using
      (Iso.homCongr (F.mapIso e) (F.mapIso d)).bijective.comp h
  exact (Function.Bijective.of_comp_iff _ (Iso.homCongr e d).bijective).1 hc

variable [HasShift C ℤ] [HasShift T ℤ] [F.CommShift ℤ]

lemma homComparison_bijective_shift_both {X Y : C}
    (h : Function.Bijective (F.map (X := X) (Y := Y))) (n : ℤ) :
    Function.Bijective (F.map (X := X⟦n⟧) (Y := Y⟦n⟧)) := by
  constructor
  · intro f g hfg
    obtain ⟨f, rfl⟩ := (shiftFunctor C n).map_surjective f
    obtain ⟨g, rfl⟩ := (shiftFunctor C n).map_surjective g
    have he := congrArg (fun k => k ≫ (F.commShiftIso n).hom.app Y) hfg
    rw [F.commShiftIso_hom_naturality, F.commShiftIso_hom_naturality] at he
    have hh := (cancel_epi ((F.commShiftIso n).hom.app X)).1 he
    exact congrArg (fun k => (shiftFunctor C n).map k)
      (h.1 ((shiftFunctor T n).map_injective hh))
  · intro g
    let t := (shiftFunctor T n).preimage
      ((F.commShiftIso n).inv.app X ≫ g ≫ (F.commShiftIso n).hom.app Y)
    obtain ⟨f, hf⟩ := h.2 t
    refine ⟨f⟦n⟧', ?_⟩
    apply (cancel_mono ((F.commShiftIso n).hom.app Y)).1
    rw [F.commShiftIso_hom_naturality, hf]
    dsimp only [t]
    rw [Functor.map_preimage]
    simp only [← Category.assoc, Iso.hom_inv_id_app]
    exact congrArg (fun k => k ≫ (F.commShiftIso n).hom.app Y) (Category.id_comp g)

/-- 固定した終域に対し、任意の始域からの関手の射写像が全単射。 -/
def homComparisonTarget : ObjectProperty C :=
  fun Y => ∀ X, Function.Bijective (F.map (X := X) (Y := Y))

instance homComparisonTargetClosedUnderIso :
    (homComparisonTarget F).IsClosedUnderIsomorphisms where
  of_iso e h X := homComparison_bijective_of_iso F (Iso.refl X) e (h X)

instance homComparisonTargetStableUnderShift :
    (homComparisonTarget F).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun Y h X => by
    let X' := (shiftFunctor C n).objPreimage X
    exact homComparison_bijective_of_iso F ((shiftFunctor C n).objObjPreimageIso X)
      (Iso.refl (Y⟦n⟧)) (homComparison_bijective_shift_both F (h X') n)⟩

end SerrePositivity.DifferentialGraded
