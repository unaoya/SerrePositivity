module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PinchedTopCoordinates
/-!
概要：左右 pinched Hom の明示同型の最上成分は、左単体の全頂点成分の次数符号倍である。
方針：線形反転と dg 反対模型の二つの反転符号を合成する。
規約：全次数を扱い、元の実 HA 成分との異種等号で比較する。
使われ方：固定終点の回収写像と右 Hom 同型の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgCoherentBarReverse_univ (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse (Finset.univ : Finset (Fin (n + 1))) = Finset.univ := by
  ext i
  simp

lemma dgCoherentBarLinearReflectionSign_op_sign (c : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign c * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (c + 1) =
      ((c : ℤ) - 1).negOnePow := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign
  rw [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).mpr
  refine ⟨(c.choose 2 : ℤ), ?_⟩
  rw [Nat.choose_succ_succ' c 1, Nat.choose_one_right]
  push_cast
  omega

lemma dgCoherentBarOpSimplex_full_hom_heq {R : Type u} [CommRing R]
    {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C (n + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex s).hom Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n) (by simp; omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (n + 2) •
        s.hom Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n) (by simp; omega)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op]
  simp only [id_eq, Finset.card_univ, Fintype.card_fin,
    dgCoherentBarReverse_univ]
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq (R := R) (C := C)
    (congrArg s.obj (Fin.rev_last (n + 1))) (congrArg s.obj (Fin.rev_zero (n + 1))) rfl
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree s.toSimplexData rfl
    (Fin.rev_last (n + 1)) (Fin.rev_zero (n + 1)) rfl

variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)

lemma dgCoherentBarLeftRightHomIso_top {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPinchedTop R C x y
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLeftRightHomIso R C x y).hom.app (Opposite.op ⦋n⦌) s))
      ((n : ℤ).negOnePow • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n s).hom Finset.univ 0 (Fin.last (n + 1))
        (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n) (by simp; omega)) := by
  have hComp := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLeftRightHomIso_component R C x y s Finset.univ (-(n : ℤ))
    Finset.univ_nonempty (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, dgCoherentBarReverse_univ] at hComp
  have hTop := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPinchedTop_hom_heq R Cᵒᵖ (Opposite.op y) (Opposite.op x)
    (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R C x y).hom.app _ s))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso_hom_val] at hTop
  have hRaw := hTop.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarOpSimplex_full_hom_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n s))
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedSimplex_obj_zero R C (x := x) (y := y) s
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedSimplex_obj_ne_zero R C (x := x) (y := y) s (Fin.last (n + 1))
    (ne_of_gt (show (0 : Fin (n + 2)) < Fin.last (n + 1) by change 0 < n + 1; omega))
  have hScalar := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq (R := R) (C := C) hx.symm hy.symm rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign (n + 1)) _ _ hRaw
  rw [smul_smul] at hScalar
  have hSign : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign (n + 1) * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (n + 2) =
      (n : ℤ).negOnePow := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
      dgCoherentBarLinearReflectionSign_op_sign (n + 1)
  rw [hSign] at hScalar
  exact hComp.trans hScalar

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
