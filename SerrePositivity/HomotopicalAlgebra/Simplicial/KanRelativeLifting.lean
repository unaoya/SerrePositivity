module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-! # Relative homotopy extension from the actual boundary pushout-product lift

No monomorphism or weak-equivalence hypothesis is needed once the
specified lifting property has been supplied.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.KanRelativeLifting
variable {A B K : SSet.{v}} (i : A ⟶ B)

abbrev boundaryProduct := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
  (SSet.boundary 1).ι

lemma exists_extension
    (hl : HasLiftingProperty (boundaryProduct i).ι (terminal.from K))
    (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    ∃ V : SSet.Homotopy f g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h := by
  let pp := boundaryProduct i
  have : HasLiftingProperty pp.ι (terminal.from K) := hl
  let b := pp.isPushout.desc (LargeParameterHomotopy.boundaryMap f g) H.h
    (KanHomotopyExtension.boundary_compatibility i f g H)
  let sq : CommSq b pp.ι (terminal.from K) (terminal.from _) := ⟨by simp⟩
  have hb : B ◁ (SSet.boundary 1).ι ≫ sq.lift =
      LargeParameterHomotopy.boundaryMap f g := by
    rw [show B ◁ (SSet.boundary 1).ι = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hH : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = H.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }, hH⟩
  · change SSet.ι₀ ≫ sq.lift = f
    rw [← LargeParameterHomotopy.section_zero B, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = g
    rw [← LargeParameterHomotopy.section_one B, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)


end SerrePositivity.SimplicialModel.KanRelativeLifting
