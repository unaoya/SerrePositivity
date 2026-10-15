module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleSmallObject

/-! # Transport of generated factorizations across hom-universe shrinking

The original category and its actual generating class are retained. Only the
hom universe used internally by the small-object accessibility proof is shrunk.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

-- ShrinkHoms and Arrow are type synonyms. Unfold them while checking
-- dependent hom, lifting-property and naturality expressions, as in Mathlib.
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Smith.AccessibleHomTransport
variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

abbrev forward : C ⥤ ShrinkHoms C := ShrinkHoms.functor.{w} C
abbrev backward : ShrinkHoms C ⥤ C := ShrinkHoms.inverse.{w} C

@[simp] lemma backward_forward_map {X Y : C} (f : X ⟶ Y) :
    (backward (C := C)).map ((forward (C := C)).map f) = f :=
  (equivShrink (X ⟶ Y)).symm_apply_apply f

@[simp] lemma forward_backward_map {X Y : ShrinkHoms C} (f : X ⟶ Y) :
    (forward (C := C)).map ((backward (C := C)).map f) = f :=
  (equivShrink _).apply_symm_apply f

abbrev generators (I : MorphismProperty C) : MorphismProperty (ShrinkHoms C) :=
  MorphismProperty.ofHoms (fun i : I.toSet ↦ (forward (C := C)).map i.val.hom)

lemma generators_rlp_iff (I : MorphismProperty C)
    {X Y : ShrinkHoms C} (p : X ⟶ Y) :
    (generators I).rlp p ↔ I.rlp ((backward (C := C)).map p) := by
  constructor
  · intro hp A B i hi
    have h := hp ((forward (C := C)).map i) (MorphismProperty.ofHoms.mk (f := fun j : I.toSet ↦
      (forward (C := C)).map j.val.hom) ⟨Arrow.mk i, hi⟩)
    have := ((backward (C := C)).hasLiftingProperty_iff_of_isEquivalence _ _).2 h
    simpa only [backward_forward_map, forward, backward, ShrinkHoms.functor_obj,
      ShrinkHoms.inverse_obj, ShrinkHoms.fromShrinkHoms, ShrinkHoms.toShrinkHoms] using this
  · intro hp A B i hi
    obtain ⟨j⟩ := hi
    have h := hp j.val.hom j.property
    apply ((backward (C := C)).hasLiftingProperty_iff_of_isEquivalence _ _).1
    simpa only [backward_forward_map, forward, backward, ShrinkHoms.functor_obj,
      ShrinkHoms.inverse_obj, ShrinkHoms.fromShrinkHoms, ShrinkHoms.toShrinkHoms] using h

lemma generators_llp_rlp_iff (I : MorphismProperty C)
    {X Y : ShrinkHoms C} (i : X ⟶ Y) :
    (generators I).rlp.llp i ↔ I.rlp.llp ((backward (C := C)).map i) := by
  constructor
  · intro hi A B p hp
    have hp' : (generators I).rlp ((forward (C := C)).map p) := by
      apply (generators_rlp_iff I _).2
      simpa only [backward_forward_map, forward, backward, ShrinkHoms.functor_obj,
      ShrinkHoms.inverse_obj, ShrinkHoms.fromShrinkHoms, ShrinkHoms.toShrinkHoms] using hp
    have h := hi _ hp'
    have := ((backward (C := C)).hasLiftingProperty_iff_of_isEquivalence _ _).2 h
    simpa only [backward_forward_map, forward, backward, ShrinkHoms.functor_obj,
      ShrinkHoms.inverse_obj, ShrinkHoms.fromShrinkHoms, ShrinkHoms.toShrinkHoms] using this
  · intro hi A B p hp
    have h := hi _ ((generators_rlp_iff I p).1 hp)
    exact ((backward (C := C)).hasLiftingProperty_iff_of_isEquivalence _ _).1 h

variable (I : MorphismProperty C)
  (d : MorphismProperty.FunctorialFactorizationData (generators I).rlp.llp (generators I).rlp)

/-- Pull the specified data back to the original category and original classes. -/
def factorization : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp where
  Z := (forward (C := C)).mapArrow ⋙ d.Z ⋙ backward
  i :=
    { app f := (backward (C := C)).map (d.i.app ((forward (C := C)).mapArrow.obj f))
      naturality f g φ := by
        have h := congrArg (fun k ↦ (backward (C := C)).map k)
          (d.i.naturality ((forward (C := C)).mapArrow.map φ))
        simp only [Functor.map_comp] at h
        change (backward (C := C)).map ((forward (C := C)).map φ.left) ≫
            (backward (C := C)).map (d.i.app ((forward (C := C)).mapArrow.obj g)) =
          (backward (C := C)).map (d.i.app ((forward (C := C)).mapArrow.obj f)) ≫
            (backward (C := C)).map (d.Z.map ((forward (C := C)).mapArrow.map φ)) at h
        rw [backward_forward_map] at h
        exact h }
  p :=
    { app f := (backward (C := C)).map (d.p.app ((forward (C := C)).mapArrow.obj f))
      naturality f g φ := by
        have h := congrArg (fun k ↦ (backward (C := C)).map k)
          (d.p.naturality ((forward (C := C)).mapArrow.map φ))
        simp only [Functor.map_comp] at h
        change (backward (C := C)).map (d.Z.map ((forward (C := C)).mapArrow.map φ)) ≫
            (backward (C := C)).map (d.p.app ((forward (C := C)).mapArrow.obj g)) =
          (backward (C := C)).map (d.p.app ((forward (C := C)).mapArrow.obj f)) ≫
            (backward (C := C)).map ((forward (C := C)).map φ.right) at h
        rw [backward_forward_map] at h
        exact h }
  fac := by
    apply NatTrans.ext
    funext f
    change (backward (C := C)).map (d.i.app ((forward (C := C)).mapArrow.obj f)) ≫
      (backward (C := C)).map (d.p.app ((forward (C := C)).mapArrow.obj f)) = f.hom
    rw [← Functor.map_comp, d.fac_app]
    exact backward_forward_map f.hom
  hi f := (generators_llp_rlp_iff I _).1 (d.hi _)
  hp f := (generators_rlp_iff I _).1 (d.hp _)

lemma factorization_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [d.Z.IsCardinalAccessible κ] : (factorization I d).Z.IsCardinalAccessible κ := by
  have : (forward (C := C)).mapArrow.IsCardinalAccessible κ := inferInstance
  have : (backward (C := C)).IsCardinalAccessible κ := inferInstance
  exact inferInstanceAs
    (((forward (C := C)).mapArrow ⋙ d.Z ⋙ backward).IsCardinalAccessible κ)

end SerrePositivity.Smith.AccessibleHomTransport
