module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension

/-! # Extend a specified interval over its specified base along a Kan fibration

One whole endpoint, the original restricted interval, and the whole base
interval are all retained. The base need not itself be a Kan complex.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanFibrationEndpointExtension
variable {A T E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (i : A ⟶ T) [Mono i]

include hp in
lemma exists_from_one (b : T ⟶ E) (a : A ⟶ E) (H : SSet.Homotopy a (i ≫ b))
    (q : T ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ B)
    (hb : b ≫ p = SSet.ι₁ ≫ q)
    (hH : H.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ ∃ V : SSet.Homotopy g b,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h ∧ V.h ≫ p = q := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.stdSimplex.δ (0 : Fin 2))
  have ha : SSet.anodyneExtensions pp.ι :=
    SSet.anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 0 1 (by decide))
  have : HasLiftingProperty pp.ι p := ha _ hp
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 0) ≫ (fst T _ ≫ b) =
      A ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ H.h := by
    rw [HomotopyEndpointComparison.face_one H]
    exact whiskerRight_fst_assoc i _ b
  let u := pp.isPushout.desc (fst T _ ≫ b) H.h hc
  have hface : (fst T (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≫ b) ≫ p =
      T ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ q := by
    rw [Category.assoc, hb]
    have he : T ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst T _ ≫ SSet.ι₁ := by
      rw [SSet.stdSimplex.δ_zero_eq_const]
      rfl
    rw [he, Category.assoc]
  have hw : u ≫ p = pp.ι ≫ q := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc,
        ← Category.assoc, pp.inl_ι]
      exact hface
    · rw [← Category.assoc, pp.isPushout.inr_desc,
        ← Category.assoc, pp.inr_ι]
      exact hH
  let sq : CommSq u pp.ι p q := ⟨hw⟩
  have ho : T ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ sq.lift = fst T _ ≫ b := by
    rw [show T ◁ SSet.stdSimplex.δ (0 : Fin 2) = pp.inl ≫ pp.ι from pp.inl_ι.symm,
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
  refine ⟨g, hg, { h := sq.lift, h₀ := rfl, h₁ := ?_, rel := ?_ }, hr, sq.fac_right⟩
  · change SSet.ι₁ ≫ sq.lift = b
    rw [← LargeParameterHomotopy.section_one T, Category.assoc, ho]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)


include hp in
lemma exists_from_zero (b : T ⟶ E) (a : A ⟶ E) (H : SSet.Homotopy (i ≫ b) a)
    (q : T ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ B)
    (hb : b ≫ p = SSet.ι₀ ≫ q)
    (hH : H.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ ∃ V : SSet.Homotopy b g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h ∧ V.h ≫ p = q := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.stdSimplex.δ (1 : Fin 2))
  have ha : SSet.anodyneExtensions pp.ι :=
    SSet.anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 1 0 (by decide))
  have : HasLiftingProperty pp.ι p := ha _ hp
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 0) ≫ (fst T _ ≫ b) =
      A ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ H.h := by
    rw [HomotopyEndpointComparison.face_zero H]
    exact whiskerRight_fst_assoc i _ b
  let u := pp.isPushout.desc (fst T _ ≫ b) H.h hc
  have hface : (fst T (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≫ b) ≫ p =
      T ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ q := by
    rw [Category.assoc, hb]
    have he : T ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst T _ ≫ SSet.ι₀ := by
      rw [SSet.stdSimplex.δ_one_eq_const]
      rfl
    rw [he, Category.assoc]
  have hw : u ≫ p = pp.ι ≫ q := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc,
        ← Category.assoc, pp.inl_ι]
      exact hface
    · rw [← Category.assoc, pp.isPushout.inr_desc,
        ← Category.assoc, pp.inr_ι]
      exact hH
  let sq : CommSq u pp.ι p q := ⟨hw⟩
  have ho : T ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ sq.lift = fst T _ ≫ b := by
    rw [show T ◁ SSet.stdSimplex.δ (1 : Fin 2) = pp.inl ≫ pp.ι from pp.inl_ι.symm,
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
  refine ⟨g, hg, { h := sq.lift, h₀ := ?_, h₁ := rfl, rel := ?_ }, hr, sq.fac_right⟩
  · change SSet.ι₀ ≫ sq.lift = b
    rw [← LargeParameterHomotopy.section_zero T, Category.assoc, ho]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

end SerrePositivity.SimplicialModel.KanFibrationEndpointExtension
