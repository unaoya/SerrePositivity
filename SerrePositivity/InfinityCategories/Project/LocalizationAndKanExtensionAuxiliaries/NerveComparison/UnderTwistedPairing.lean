module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingNerve
/-! 同じ通常圏のUnderの族をcosliceとtwisted pairingで表示した全写像の照合。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

private def collapseStandard (n : ℕ) : (Δ[n+n+1] : SSet.{u}) ⟶ Δ[n+1] :=
  (edgewiseWeightIso n).inv ≫ cosliceEdgewiseCollapse ⦋n⦌ ≫ (pointJoinStdSimplexIso n).hom
private def collapseOrder (n : ℕ) : Fin (n+n+1+1) →o Fin (n+2) :=
  (stdSimplex.objEquiv (SSet.yonedaEquiv (collapseStandard.{u} n))).toOrderHom
private lemma collapseOrder_map (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom (collapseOrder.{u} n)) = collapseStandard.{u} n :=
  SSet.yonedaEquiv.symm_apply_apply _
private lemma collapseStandard_left (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom n n)) ≫ collapseStandard.{u} n =
      (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) : Δ[n] ⟶ Δ[0]) ≫
        joinInl Δ[0] Δ[n] ≫ (pointJoinStdSimplexIso n).hom := by
  have hl : stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom n n)) =
      (stdSimplex.opIso ⦋n⦌).inv ≫ joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫
        (edgewiseWeightIso n).hom := by
    rw [edgewiseWeightIso_inl, Iso.inv_hom_id_assoc]
  rw [hl, collapseStandard]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [cosliceEdgewiseCollapse, joinInl_joinMap_assoc, ← Category.assoc, SSet.comp_const]
private lemma collapseStandard_right (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom (joinRightOrderHom n n)) ≫ collapseStandard.{u} n =
      stdSimplex.δ (0 : Fin (n+2)) := by
  rw [← edgewiseWeightIso_inr, collapseStandard]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [cosliceEdgewiseCollapse, joinInr_joinMap_assoc, Category.id_comp,
    pointJoinStdSimplexIso_inr]
private lemma collapseOrder_left (n : ℕ) (i : Fin (n+1)) :
    collapseOrder.{u} n (joinLeftOrderHom n n i) = 0 := by
  have h := congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n+1] =>
    (stdSimplex.objEquiv (SSet.yonedaEquiv f)).toOrderHom i) (collapseStandard_left.{u} n)
  rw [← collapseOrder_map] at h
  change collapseOrder.{u} n (joinLeftOrderHom n n i) = _ at h
  rw [pointJoinStdSimplexIso_inl_vertex] at h
  exact h
private lemma collapseOrder_right (n : ℕ) (i : Fin (n+1)) :
    collapseOrder.{u} n (joinRightOrderHom n n i) = i.succ := by
  have h := congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n+1] =>
    (stdSimplex.objEquiv (SSet.yonedaEquiv f)).toOrderHom i) (collapseStandard_right.{u} n)
  rw [← collapseOrder_map] at h
  exact h
private lemma collapseOrder_left_val (n : ℕ) (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    collapseOrder.{u} n i = 0 := by
  have he : i = joinLeftOrderHom n n ⟨i.val, hi⟩ := Fin.ext rfl
  rw [he, collapseOrder_left]
private lemma collapseOrder_right_val (n : ℕ) (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    collapseOrder.{u} n i = (twistedPairingRightIndex i hi).succ := by
  have he : i = joinRightOrderHom n n (twistedPairingRightIndex i hi) := by
    apply Fin.ext
    change i.val = n+1+(i.val-(n+1))
    omega
  calc
    collapseOrder.{u} n i = collapseOrder.{u} n
      (joinRightOrderHom n n (twistedPairingRightIndex i hi)) := congrArg _ he
    _ = _ := collapseOrder_right n _
private lemma collapseUnderChain {C : Type u} [Category.{u} C] (c : C)
    {n : ℕ} (σ : Fin (n+1) ⥤ Under c) :
    (collapseOrder.{u} n).monotone.functor ⋙ nerveUnderChain c σ =
      twistedPairingSimplex ((Functor.const (Under c)).obj (Opposite.op c))
        (Under.forget c) (fun i => i.hom) σ := by
  let L := (Functor.const (Under c)).obj (Opposite.op c)
  let R := Under.forget c
  let s := fun i : Under c => i.hom
  apply Functor.hext
  · intro i
    by_cases hi : i.val < n+1
    · change (nerveUnderChain c σ).obj (collapseOrder.{u} n i) = _
      rw [collapseOrder_left_val n i hi]
      exact (twistedPairingSimplexObj_left L R σ i hi).symm
    · change (nerveUnderChain c σ).obj (collapseOrder.{u} n i) = _
      rw [collapseOrder_right_val n i hi]
      exact (twistedPairingSimplexObj_right L R σ i hi).symm
  · intro i j f
    change HEq ((nerveUnderChain c σ).map ((collapseOrder.{u} n).monotone.functor.map f))
      (twistedPairingSimplexMap L R s σ i j (leOfHom f))
    by_cases hi : i.val < n+1
    · by_cases hj : j.val < n+1
      · have hL := twistedPairingThinMap_heq (nerveUnderChain c σ)
          (collapseOrder_left_val n i hi) (collapseOrder_left_val n j hj)
          (f := (collapseOrder.{u} n).monotone.functor.map f) (g := 𝟙 0)
        have hR := twistedPairingSimplexMap_left_heq L R s σ i j (leOfHom f) hi hj
        exact hL.trans ((heq_of_eq ((nerveUnderChain c σ).map_id 0)).trans hR.symm)
      · have hL := twistedPairingThinMap_heq (nerveUnderChain c σ)
          (collapseOrder_left_val n i hi) (collapseOrder_right_val n j hj)
          (f := (collapseOrder.{u} n).monotone.functor.map f)
          (g := homOfLE (Fin.zero_le _))
        have hR := twistedPairingSimplexMap_cross_heq L R s σ i j (leOfHom f) hi hj
        refine hL.trans ((heq_of_eq (nerveUnderChain_map_zero_succ c σ _)).trans ?_)
        have hcross : twistedPairingCross L R s σ (twistedPairingLeftIndex i hi)
            (twistedPairingRightIndex j hj) = (σ.obj (twistedPairingRightIndex j hj)).hom := by
          change (𝟙 c) ≫ (σ.obj 0).hom ≫
            (σ.map (homOfLE (Fin.zero_le (twistedPairingRightIndex j hj)))).right = _
          rw [Category.id_comp]
          exact Under.w (σ.map (homOfLE (Fin.zero_le _)))
        exact (heq_of_eq hcross).symm.trans hR.symm
    · have hj : ¬ j.val < n+1 := fun h => hi (lt_of_le_of_lt (leOfHom f) h)
      have hL := twistedPairingThinMap_heq (nerveUnderChain c σ)
        (collapseOrder_right_val n i hi) (collapseOrder_right_val n j hj)
        (f := (collapseOrder.{u} n).monotone.functor.map f)
        (g := homOfLE (show (twistedPairingRightIndex i hi).succ ≤
          (twistedPairingRightIndex j hj).succ by
            apply Fin.succ_le_succ_iff.mpr
            dsimp [twistedPairingRightIndex]
            exact Nat.sub_le_sub_right (leOfHom f) _))
      have hR := twistedPairingSimplexMap_right_heq L R s σ i j (leOfHom f) hi hj
      exact hL.trans hR.symm
/-- Underの同じ実射の全族は、coslice表示から同じtwisted pairingを厳密に回収する。 -/
lemma nerveUnderMap_comp_cosliceTwistedArrowMap {C : Type u} [Category.{u} C] (c : C) :
    nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const (Under c)).obj (Opposite.op c)) (Under.forget c)
        (fun i => i.hom) (fun {_ _} f => by simp) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change cosliceEdgewiseCollapse ⦋n⦌ ≫ (pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := nerve C)).symm (nerveUnderChain c σ) =
    (edgewiseWeightIso n).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm
      (twistedPairingSimplex ((Functor.const (Under c)).obj (Opposite.op c))
        (Under.forget c) (fun i => i.hom) σ)
  have hc : cosliceEdgewiseCollapse.{u} ⦋n⦌ ≫ (pointJoinStdSimplexIso n).hom =
      (edgewiseWeightIso n).hom ≫
        stdSimplex.map (SimplexCategory.mkHom (collapseOrder.{u} n)) := by
    rw [collapseOrder_map, collapseStandard, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hc, Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  change (edgewiseWeightIso n).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm
      ((collapseOrder.{u} n).monotone.functor ⋙ nerveUnderChain c σ) = _
  rw [collapseUnderChain]
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
end
