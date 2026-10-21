module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceFiber
public import SerrePositivity.InfinityCategories.Derived.DGLeftPinchedLinearCoordinates
public import SerrePositivity.InfinityCategories.Derived.DGGradedPrecompositionWhisker
/-!
概要：同じ実 coslice fiber の前合成は、左 Hom の全線形係数への同じ閉前合成である。
方針：実単体の閉始点細分を回収し、反対模型の符号と端点輸送を異種等号で比較する。
規約：全次数・全係数の等式。使われ方：実 fiber 射の同値性の Hom 鎖写像による判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DGNerveOppositeIndex SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (x q y : D) (s : ForgetEnrichment.of (Complex R) q ⟶ ForgetEnrichment.of (Complex R) x)
/-- 実 fiber 射の左 Hom 表示は、元の同じ全単体の閉始点細分。 -/
lemma dgCoslicePrecomposeLeftMap_refinement {n : ℕ}
    (t : (pinchedHomLeft (X := dgNerve R D)
      (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    pinchedLeftSimplexVal n ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t) =
      dgSimplexInitialRefinement R D (pinchedLeftSimplexVal n t) q
        (dgClosedTargetTransport R D s (dgLeftPinchedSimplex_obj_zero R D t).symm) := by
  rw [dgCoslicePrecomposeLeftMap_simplex]
  unfold dgCoslicePrecomposeCoordinate
  apply dgSimplexInitialRefinement_congr
    (dgLeftPinchedCosliceFiberIso_simplex (X := dgNerve R D)
      (Simplex.vertex (A := R) x) (Simplex.vertex y) t) q q
  exact (dgClosedTargetTransport_edge R D s _).trans
    (dgClosedTargetTransport_edge R D s _).symm
/-- 実 fiber 射の左 Hom 表示は、同じ標準 Hom 鎖前合成を全線形係数に適用する。 -/
lemma dgCoslicePrecomposeLeftMap_linear {n : ℕ}
    (t : (pinchedHomLeft (X := dgNerve R D)
      (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    dgLeftPinchedLinearEquiv R D q y n
      ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t) =
    pinchedLinearSimplexMap (A := R) (D := Dᵒᵖ) (E := Dᵒᵖ)
      (x := Opposite.op y) (y := Opposite.op x)
      (x' := Opposite.op y) (y' := Opposite.op q)
      (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) y))
      (dgLeftPinchedLinearEquiv R D x y n t) := by
  apply Subtype.ext
  funext i
  obtain ⟨⟨J, k⟩, hJ, hk⟩ := i
  change J.Nonempty at hJ
  change k = 1 - (J.card : ℤ) at hk
  change (dgLeftPinchedLinearEquiv R D q y n
      ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t)).val.component J k hJ hk =
    (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) y)).f k
      ((dgLeftPinchedLinearEquiv R D x y n t).val.component J k hJ hk)
  have hl := dgLeftPinchedLinearEquiv_component_heq R D
    ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t) J k hJ hk
  have hr := dgLeftPinchedLinearEquiv_component_heq R D t J k hJ hk
  rw [dgCoslicePrecomposeLeftMap_refinement] at hl
  dsimp only [DGNerveOppositeData.opSimplex, DGNerveOppositeData.op] at hl hr
  dsimp only [id] at hl hr
  let T := pinchedLeftSimplexVal n t
  let sT := dgClosedTargetTransport R D s (dgLeftPinchedSimplex_obj_zero R D t).symm
  let b := (J.min' hJ).castSucc.rev
  have hb0 : b ≠ 0 := by
    intro he
    have hh := congrArg Fin.rev he
    dsimp only [b] at hh
    simp only [Fin.rev_rev, Fin.rev_zero] at hh
    exact (Fin.castSucc_lt_last (J.min' hJ)).ne hh
  let I := reverse (withLast J)
  have hI : 2 ≤ I.card := two_le_card_reverse (two_withLast hJ)
  have ha : (0 : Fin (n + 2)) = I.min' (Index.nonempty hI) := by
    simpa only [Fin.rev_last] using
      reverse_min (two_withLast hJ) (max_withLast J _)
  have hb : b = I.max' (Index.nonempty hI) :=
    reverse_max (two_withLast hJ) (min_withLast hJ _)
  have hdeg : k = 2 - (I.card : ℤ) := by
    dsimp only [I]
    rw [card_reverse, card_withLast]
    omega
  have hZero (a : Simplex R D (n + 1)) :
      HEq (DGNerveOppositeSigns.sign (withLast J).card •
        a.hom I (Fin.last (n + 1)).rev b k hI
          (reverse_min (two_withLast hJ) (max_withLast J _)) hb hdeg)
        (DGNerveOppositeSigns.sign (withLast J).card • a.hom I 0 b k hI ha hb hdeg) := by
    apply gradedHom_units_smul_heq (congrArg a.obj (Fin.rev_last _)) rfl rfl
    exact a.toSimplexData.hom_heq_of_indices_degree rfl (Fin.rev_last _) rfl rfl
  have hl := hl.trans (hZero (dgSimplexInitialRefinement R D T q sT))
  have hr := hr.trans (hZero T)
  have hRef := dgSimplexDataInitialRefinement_hom_from_zero R D T.toSimplexData q sT
    I b k hI ha hb hdeg
  have hSmul := gradedHom_units_smul_heq
    (dgSimplexInitialRefinement_obj_zero R D T q sT)
    (dgSimplexInitialRefinement_obj_ne_zero R D T q sT b hb0) rfl
    (DGNerveOppositeSigns.sign (withLast J).card) _ _ hRef
  have hp := dgGradedPrecompose_heq R D k rfl
    (dgLeftPinchedSimplex_obj_zero R D t).symm
    (dgLeftPinchedSimplex_obj_ne_zero R D t b hb0).symm _ _ hr s sT
    (dgClosedTargetTransport_edge R D s _).symm
  rw [dgGradedPrecompose_units_smul] at hp
  exact eq_of_heq (hl.trans (hSmul.trans (hp.symm.trans
    (heq_of_eq (dgGradedPrecompose_eq_whisker_f R D k _ s)))))
end SerrePositivity.InfinityCategories
