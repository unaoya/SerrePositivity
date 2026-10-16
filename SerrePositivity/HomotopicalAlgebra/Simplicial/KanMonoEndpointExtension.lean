module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-! # Extend a prescribed whole homotopy along a monomorphism with one endpoint fixed

The original endpoint map and original restricted interval map are both
retained. Only the Kan lifting property is used, in any value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanMonoEndpointExtension
variable {A B K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hK in
lemma exists_from_zero (b : B ⟶ K) (a : A ⟶ K) (H : SSet.Homotopy (i ≫ b) a) :
    ∃ g : B ⟶ K, i ≫ g = a ∧ ∃ H' : SSet.Homotopy b g,
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ H'.h = H.h := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.stdSimplex.δ (1 : Fin 2))
  have ha : SSet.anodyneExtensions pp.ι :=
    SSet.anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 1 0 (by decide))
  have : HasLiftingProperty pp.ι (terminal.from K) := ha _ hK
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 0) ≫ (fst B _ ≫ b) =
      A ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ H.h := by
    rw [HomotopyEndpointComparison.face_zero H]
    exact whiskerRight_fst_assoc i _ b
  let u := pp.isPushout.desc (fst B _ ≫ b) H.h hc
  let sq : CommSq u pp.ι (terminal.from K) (terminal.from _) := ⟨by simp⟩
  have hz : B ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ sq.lift = fst B _ ≫ b := by
    rw [show B ◁ SSet.stdSimplex.δ (1 : Fin 2) = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hr : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = H.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  let g := SSet.ι₁ ≫ sq.lift
  have hg : i ≫ g = a := by
    dsimp only [g]
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hr]
    exact H.h₁
  refine ⟨g, hg, { h := sq.lift, h₀ := ?_, h₁ := rfl, rel := ?_ }, hr⟩
  · change SSet.ι₀ ≫ sq.lift = b
    rw [← LargeParameterHomotopy.section_zero B, Category.assoc, hz]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include hK in
lemma exists_from_one (b : B ⟶ K) (a : A ⟶ K) (H : SSet.Homotopy a (i ≫ b)) :
    ∃ g : B ⟶ K, i ≫ g = a ∧ ∃ H' : SSet.Homotopy g b,
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ H'.h = H.h := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.stdSimplex.δ (0 : Fin 2))
  have ha : SSet.anodyneExtensions pp.ι :=
    SSet.anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 0 1 (by decide))
  have : HasLiftingProperty pp.ι (terminal.from K) := ha _ hK
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 0) ≫ (fst B _ ≫ b) =
      A ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ H.h := by
    rw [HomotopyEndpointComparison.face_one H]
    exact whiskerRight_fst_assoc i _ b
  let u := pp.isPushout.desc (fst B _ ≫ b) H.h hc
  let sq : CommSq u pp.ι (terminal.from K) (terminal.from _) := ⟨by simp⟩
  have ho : B ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ sq.lift = fst B _ ≫ b := by
    rw [show B ◁ SSet.stdSimplex.δ (0 : Fin 2) = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hr : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = H.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  let g := SSet.ι₀ ≫ sq.lift
  have hg : i ≫ g = a := by
    dsimp only [g]
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hr]
    exact H.h₀
  refine ⟨g, hg, { h := sq.lift, h₀ := rfl, h₁ := ?_, rel := ?_ }, hr⟩
  · change SSet.ι₁ ≫ sq.lift = b
    rw [← LargeParameterHomotopy.section_one B, Category.assoc, ho]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

end SerrePositivity.SimplicialModel.KanMonoEndpointExtension
