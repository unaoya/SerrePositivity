module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRetractionRightLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection

/-! # Localized equivalences which are Kan fibrations over a Kan base lift all monos

Kan tests first give a homotopy inverse. Interval lifting makes its section
identity strict. Actual Kan homotopies then supply the retraction contraction.
The construction uses no model structure on the value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanFibrationLocalizedLifting
variable {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)

include hp in
lemma exists_section_of_homotopy (g : B ⟶ E) (H : SSet.Homotopy (g ≫ p) (𝟙 B)) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B ∧ Nonempty (SSet.Homotopy g s) := by
  have : HasLiftingProperty (SSet.ι₀ (X := B)) p :=
    AnodyneHomotopy.endpoint_zero_anodyne B _ hp
  let sq : CommSq g SSet.ι₀ p H.h := ⟨H.h₀.symm⟩
  let s := SSet.ι₁ ≫ sq.lift
  have hs : s ≫ p = 𝟙 B := by
    dsimp only [s]
    rw [Category.assoc, sq.fac_right, H.h₁]
  refine ⟨s, hs, ⟨{ h := sq.lift, h₀ := sq.fac_left, h₁ := rfl, rel := ?_ }⟩⟩
  apply NatTrans.ext
  funext n
  exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include hp in
lemma exists_retraction_of_tests
    (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B)) (ht : KanTestDetection.Tests p) :
    ∃ s : B ⟶ E, ∃ _hs : s ≫ p = 𝟙 B, Nonempty (SSet.Homotopy (𝟙 E) (p ≫ s)) := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  have : Fibration (terminal.from B) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hB
  have : SSet.KanComplex B := (isFibrant_iff B).mpr inferInstance
  have : SSet.KanComplex E := isFibrant_of_fibration p
  have hE : SSet.modelCategoryQuillen.J.rlp (terminal.from E) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨x, hx⟩ := (ht E hE).surjective (HomotopyClasses.mk (𝟙 E))
  obtain ⟨g, rfl⟩ := Quot.exists_rep x
  have hpg : HomotopyClasses.mk (p ≫ g) = HomotopyClasses.mk (𝟙 E) := hx
  have hgp : HomotopyClasses.mk (g ≫ p) = HomotopyClasses.mk (𝟙 B) :=
    (ht B hB).injective (by
      simpa only [HomotopyClasses.pre_mk, HomotopyClasses.post_mk,
        Category.assoc, Category.id_comp, Category.comp_id]
        using congrArg (HomotopyClasses.post p) hpg)
  obtain ⟨Hgp⟩ := KanActualHomotopy.of_class_eq hB hgp
  obtain ⟨s, hs, ⟨W⟩⟩ := exists_section_of_homotopy p hp g Hgp
  refine ⟨s, hs, KanActualHomotopy.of_class_eq hE ?_⟩
  exact hpg.symm.trans (congrArg (HomotopyClasses.pre p) (HomotopyClasses.sound W))

include hp in
lemma of_tests (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B))
    (ht : KanTestDetection.Tests p) : (MorphismProperty.monomorphisms SSet.{v}).rlp p := by
  obtain ⟨s, hs, ⟨H⟩⟩ := exists_retraction_of_tests p hp hB ht
  exact KanRetractionRightLifting.of_homotopy p hp s hs H

include hp in
lemma of_post_tests (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B))
    (hsurj : Function.Surjective (HomotopyClasses.post p (X := B)))
    (hinj : Function.Injective (HomotopyClasses.post p (X := E))) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp p := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  have : Fibration (terminal.from B) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hB
  have : SSet.KanComplex B := (isFibrant_iff B).mpr inferInstance
  have : SSet.KanComplex E := isFibrant_of_fibration p
  have hE : SSet.modelCategoryQuillen.J.rlp (terminal.from E) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨x, hx⟩ := hsurj (HomotopyClasses.mk (𝟙 B))
  obtain ⟨g, rfl⟩ := Quot.exists_rep x
  obtain ⟨Hgp⟩ := KanActualHomotopy.of_class_eq hB hx
  obtain ⟨s, hs, _⟩ := exists_section_of_homotopy p hp g Hgp
  have heq : HomotopyClasses.mk (𝟙 E) = HomotopyClasses.mk (p ≫ s) := hinj (by
    simp only [HomotopyClasses.post_mk, Category.assoc, hs, Category.id_comp,
      Category.comp_id])
  obtain ⟨H⟩ := KanActualHomotopy.of_class_eq hE heq
  exact KanRetractionRightLifting.of_homotopy p hp s hs H

include hp in
lemma of_localized_isIso (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B))
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map p)) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp p :=
  of_tests p hp hB (KanTestDetection.tests_of_anodyneQ_isIso p hf)

include hp in
lemma boundary_rlp (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B))
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map p)) : SSet.modelCategoryQuillen.I.rlp p := by
  rw [← SSet.rlp_monomorphisms]
  exact of_localized_isIso p hp hB hf

end SerrePositivity.SimplicialModel.KanFibrationLocalizedLifting
