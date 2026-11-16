module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseStandardSimplex
/-! 同じtwisted pairingの重み・長い射列・両端交換の厳密な整合性。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

private lemma standardIso_end_hom (n : ℕ) (e : (Δ[n] : SSet.{u}) ≅ Δ[n]) :
    e.hom = 𝟙 _ := by
  have h := congrArg Iso.hom (SimplexCategory.iso_eq_iso_refl (stdSimplex.preimageIso e))
  have h' := congrArg stdSimplex.map h
  change stdSimplex.map (stdSimplex.preimage e.hom) = stdSimplex.map (𝟙 ⦋n⦌) at h'
  exact (stdSimplex.map_preimage e.hom).symm.trans (h'.trans (stdSimplex.map_id _))
private lemma nerveReverseChain_yoneda {C : Type u} [Category.{u} C] {n : ℕ}
    (τ : (nerve C) _⦋n⦌) :
    (stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map (SSet.yonedaEquiv.symm τ) ≫
      (nerveOppositeIso (C := C)).hom = SSet.yonedaEquiv.symm (nerveReverseChain τ) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change nerveReverseChain
    (((SSet.opFunctor.map (SSet.yonedaEquiv.symm τ)).app (Opposite.op ⦋n⦌))
      ((stdSimplex.opIso ⦋n⦌).inv.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 _)))) = _
  congr 1
  change (SSet.yonedaEquiv.symm τ).app (Opposite.op ⦋n⦌)
    (stdSimplex.objEquiv.symm (SimplexCategory.rev.map (𝟙 ⦋n⦌))) = τ
  rw [SimplexCategory.rev.map_id]
  have hy := SSet.yonedaEquiv_symm_app_objEquiv_symm (X := nerve C) τ (𝟙 ⦋n⦌)
  have hid : (nerve C).map (𝟙 ⦋n⦌).op = 𝟙 ((nerve C).obj (Opposite.op ⦋n⦌)) :=
    (congrArg (nerve C).map (show (𝟙 ⦋n⦌).op = 𝟙 (Opposite.op ⦋n⦌) from op_id)).trans
      ((nerve C).map_id _)
  exact hy.trans (ConcreteCategory.congr_hom hid _)

/-- 同じ重みの両端交換は、同じ通常の射列の反転を回収する。 -/
lemma twistedArrowOppositeSwap_nerve_reverse {C : Type u} [Category.{u} C] (n : ℕ)
    (τ : (nerve C) _⦋n+n+1⦌) :
    (twistedArrowOppositeSwap (nerve C)).app (Opposite.op ⦋n⦌)
      ((edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm (nerveReverseChain τ) ≫
        (nerveOppositeIso (C := C)).inv) =
      (edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm τ := by
  let y := SSet.yonedaEquiv.symm τ
  have hr : SSet.yonedaEquiv.symm (nerveReverseChain τ) ≫
        (nerveOppositeIso (C := C)).inv =
      (stdSimplex.opIso ⦋n+n+1⦌).inv ≫ SSet.opFunctor.map y := by
    apply (cancel_mono (nerveOppositeIso (C := C)).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
    exact (nerveReverseChain_yoneda τ).symm
  let e := (edgewiseWeightReverseIso.{u} ⦋n⦌).symm ≪≫
    SSet.opFunctor.mapIso (edgewiseWeightIso n ≪≫ (stdSimplex.opIso ⦋n+n+1⦌).symm) ≪≫
      SSet.opFunctorCompOpFunctorIso.app (Δ[n+n+1] : SSet.{u})
  have he : e.hom = (edgewiseWeightIso n).hom := by
    have h := standardIso_end_hom (n+n+1) ((edgewiseWeightIso n).symm ≪≫ e)
    change (edgewiseWeightIso n).inv ≫ e.hom = 𝟙 _ at h
    have ht := congrArg (fun f => (edgewiseWeightIso n).hom ≫ f) h
    simpa only [Iso.hom_inv_id_assoc, Category.comp_id] using ht
  change (edgewiseWeightReverseIso.{u} ⦋n⦌).inv ≫
    SSet.opFunctor.map ((edgewiseWeightIso n).hom ≫
      SSet.yonedaEquiv.symm (nerveReverseChain τ) ≫ (nerveOppositeIso (C := C)).inv) ≫
        (SSet.opFunctorCompOpFunctorIso.app (nerve C)).hom = _
  rw [hr, SSet.opFunctor.map_comp, SSet.opFunctor.map_comp]
  simp only [Category.assoc]
  have hn : SSet.opFunctor.map (SSet.opFunctor.map y) ≫
      (SSet.opFunctorCompOpFunctorIso.app (nerve C)).hom =
        (SSet.opFunctorCompOpFunctorIso.app (Δ[n+n+1] : SSet.{u})).hom ≫ y :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality y
  rw [hn]
  have hh := congrArg (fun f => f ≫ y) he
  simpa only [e, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    SSet.opFunctor.map_comp, Category.assoc] using hh

private lemma rev_left_index {n : ℕ} (i : Fin (n+n+1+1))
    (hi : i.val < n+1) (hr : ¬ i.rev.val < n+1) :
    twistedPairingRightIndex i.rev hr = twistedPairingLeftIndex i hi := by
  apply Fin.ext
  dsimp [twistedPairingRightIndex, twistedPairingLeftIndex]
  have := i.isLt
  omega
private lemma rev_right_index {n : ℕ} (i : Fin (n+n+1+1))
    (hi : ¬ i.val < n+1) (hr : i.rev.val < n+1) :
    twistedPairingLeftIndex i.rev hr = twistedPairingRightIndex i hi := by
  apply Fin.ext
  dsimp [twistedPairingRightIndex, twistedPairingLeftIndex]
  have := i.isLt
  omega
private lemma op_heq_of_endpoints {C : Type u} [Category.{u} C]
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : HEq f g) : HEq f.op g.op := by
  subst X' Y'
  cases h
  rfl
private lemma thin_op_heq {C : Type u} [Category.{u} C] {N : ℕ}
    (F : Fin N ⥤ C) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f).op (F.map g).op := by
  subst c d
  have he : f = g := Subsingleton.elim _ _
  subst g
  rfl
private lemma cross_op {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    {n : ℕ} (σ : Fin (n+1) ⥤ I) (a b : Fin (n+1)) :
    twistedPairingCross (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op) σ a b =
      (twistedPairingCross A B h σ b a).op := by
  change (B.map (σ.map (homOfLE (Fin.zero_le a)))).op ≫ (h (σ.obj 0)).op ≫
    A.map (σ.map (homOfLE (Fin.zero_le b))) = _
  simp only [twistedPairingCross, CategoryTheory.op_comp, Quiver.Hom.op_unop, Category.assoc]
private lemma cross_op_heq {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    {n : ℕ} (σ : Fin (n+1) ⥤ I) {a b c d : Fin (n+1)} (ha : a = c) (hb : b = d) :
    HEq (twistedPairingCross A B h σ a b).op (twistedPairingCross A B h σ c d).op := by
  subst c d
  rfl
/-- 元のpairingの全対象・全射は、反対のpairingの同じ反転射列と一致する。 -/
lemma twistedPairingSimplex_reverse {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    {n : ℕ} (σ : Fin (n+1) ⥤ I) :
    twistedPairingSimplex (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op) σ =
      nerveReverseChain (twistedPairingSimplex A B h σ) := by
  let A' := B ⋙ (opOpEquivalence C).inverse
  let h' := fun i => (h i).op
  apply CategoryTheory.Functor.hext
  · intro i
    change twistedPairingSimplexObj A' A σ i = Opposite.op (twistedPairingSimplexObj A B σ i.rev)
    by_cases hi : i.val < n+1
    · have hr : ¬ i.rev.val < n+1 := by simp only [Fin.val_rev]; omega
      rw [twistedPairingSimplexObj_left A' A σ i hi, twistedPairingSimplexObj_right A B σ i.rev hr,
        rev_left_index i hi hr]
      rfl
    · have hr : i.rev.val < n+1 := by simp only [Fin.val_rev]; have := i.isLt; omega
      rw [twistedPairingSimplexObj_right A' A σ i hi, twistedPairingSimplexObj_left A B σ i.rev hr,
        rev_right_index i hi hr]
  · intro i j f
    have hij := leOfHom f
    have hrev : j.rev ≤ i.rev := by simpa only [Fin.rev_le_rev] using hij
    change HEq (twistedPairingSimplexMap A' A h' σ i j hij)
      (twistedPairingSimplexMap A B h σ j.rev i.rev hrev).op
    by_cases hi : i.val < n+1
    · have hir : ¬ i.rev.val < n+1 := by simp only [Fin.val_rev]; omega
      by_cases hj : j.val < n+1
      · have hjr : ¬ j.rev.val < n+1 := by simp only [Fin.val_rev]; omega
        have hL := twistedPairingSimplexMap_left_heq A' A h' σ i j hij hi hj
        have hR := op_heq_of_endpoints
          (twistedPairingSimplexObj_right A B σ j.rev hjr)
          (twistedPairingSimplexObj_right A B σ i.rev hir)
          (twistedPairingSimplexMap_right_heq A B h σ j.rev i.rev hrev hjr hir)
        refine hL.trans (HEq.trans ?_ hR.symm)
        exact thin_op_heq (σ ⋙ B) (rev_left_index j hj hjr).symm (rev_left_index i hi hir).symm
      · have hjr : j.rev.val < n+1 := by simp only [Fin.val_rev]; have := j.isLt; omega
        have hL := twistedPairingSimplexMap_cross_heq A' A h' σ i j hij hi hj
        have hR := op_heq_of_endpoints
          (twistedPairingSimplexObj_left A B σ j.rev hjr)
          (twistedPairingSimplexObj_right A B σ i.rev hir)
          (twistedPairingSimplexMap_cross_heq A B h σ j.rev i.rev hrev hjr hir)
        refine hL.trans (HEq.trans (heq_of_eq (cross_op A B h σ _ _)) (HEq.trans ?_ hR.symm))
        exact cross_op_heq A B h σ (rev_right_index j hj hjr).symm (rev_left_index i hi hir).symm
    · have hj : ¬ j.val < n+1 := fun he => hi (lt_of_le_of_lt hij he)
      have hir : i.rev.val < n+1 := by simp only [Fin.val_rev]; have := i.isLt; omega
      have hjr : j.rev.val < n+1 := by simp only [Fin.val_rev]; have := j.isLt; omega
      have hL := twistedPairingSimplexMap_right_heq A' A h' σ i j hij hi hj
      have hR := op_heq_of_endpoints
        (twistedPairingSimplexObj_left A B σ j.rev hjr)
        (twistedPairingSimplexObj_left A B σ i.rev hir)
        (twistedPairingSimplexMap_left_heq A B h σ j.rev i.rev hrev hjr hir)
      refine hL.trans (HEq.trans ?_ hR.symm)
      exact twistedPairingThinMap_heq (σ ⋙ A) (rev_right_index i hi hir).symm
        (rev_right_index j hj hjr).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
end
