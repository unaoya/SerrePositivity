module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGClosedCosliceFiber
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGLeftPinchedLinearCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGGradedPrecompositionWhisker
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGNerveOppositeIndex SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (x q y : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)
/-- 実 fiber 射の左 Hom 表示は、元の同じ全単体の閉始点細分。 -/
lemma dgCoslicePrecomposeLeftMap_refinement {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R D x q y s).app _ t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement R D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport R D s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedSimplex_obj_zero R D t).symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap_simplex]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeCoordinate
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedCosliceFiberIso_simplex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) t) q q
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge R D s _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge R D s _).symm
/-- 実 fiber 射の左 Hom 表示は、同じ標準 Hom 鎖前合成を全線形係数に適用する。 -/
lemma dgCoslicePrecomposeLeftMap_linear {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R D q y n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R D x q y s).app _ t) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (A := R) (D := Dᵒᵖ) (E := Dᵒᵖ)
      (x := Opposite.op y) (y := Opposite.op x)
      (x' := Opposite.op y) (y' := Opposite.op q)
      (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R D x y n t) := by
  apply Subtype.ext
  funext i
  obtain ⟨⟨J, k⟩, hJ, hk⟩ := i
  change J.Nonempty at hJ
  change k = 1 - (J.card : ℤ) at hk
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R D q y n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R D x q y s).app _ t)).val.component J k hJ hk =
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)).f k
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R D x y n t).val.component J k hJ hk)
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv_component_heq R D
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R D x q y s).app _ t) J k hJ hk
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv_component_heq R D t J k hJ hk
  rw [dgCoslicePrecomposeLeftMap_refinement] at hl
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op] at hl hr
  dsimp only [id] at hl hr
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t
  let sT := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport R D s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedSimplex_obj_zero R D t).symm
  let b := (J.min' hJ).castSucc.rev
  have hb0 : b ≠ 0 := by
    intro he
    have hh := congrArg Fin.rev he
    dsimp only [b] at hh
    simp only [Fin.rev_rev, Fin.rev_zero] at hh
    exact (Fin.castSucc_lt_last (J.min' hJ)).ne hh
  let I := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
  have hI : 2 ≤ I.card := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ)
  have ha : (0 : Fin (n + 2)) = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
    simpa only [Fin.rev_last] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
  have hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _)
  have hdeg : k = 2 - (I.card : ℤ) := by
    dsimp only [I]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]
    omega
  have hZero (a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D (n + 1)) :
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).card •
        a.hom I (Fin.last (n + 1)).rev b k hI
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)) hb hdeg)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).card • a.hom I 0 b k hI ha hb hdeg) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq (congrArg a.obj (Fin.rev_last _)) rfl rfl
    exact a.toSimplexData.hom_heq_of_indices_degree rfl (Fin.rev_last _) rfl rfl
  have hl := hl.trans (hZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement R D T q sT))
  have hr := hr.trans (hZero T)
  have hRef := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_hom_from_zero R D T.toSimplexData q sT
    I b k hI ha hb hdeg
  have hSmul := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_obj_zero R D T q sT)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_obj_ne_zero R D T q sT b hb0) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).card) _ _ hRef
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_heq R D k rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedSimplex_obj_zero R D t).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedSimplex_obj_ne_zero R D t b hb0).symm _ _ hr s sT
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge R D s _).symm
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_units_smul] at hp
  exact eq_of_heq (hl.trans (hSmul.trans (hp.symm.trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_eq_whisker_f R D k _ s)))))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
