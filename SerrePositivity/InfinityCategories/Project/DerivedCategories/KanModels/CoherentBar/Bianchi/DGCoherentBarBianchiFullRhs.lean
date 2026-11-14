module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Bianchi.DGCoherentBarBianchiTermComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRhs

/-!
概要：末端に bar を加えた正次元の全体 HA 右辺は、元の θ と包含の合成に一致する。
方針：内部頂点ごとの実係数比較を有限和へ戻し、元の列の作用式を適用する。
規約：MC 方程式や余錐の普遍性を仮定しない。
使われ方：任意の部分集合へ制限して、Bianchi による bar の MC を結論する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiData_full_rhs_heq_boundary {n : ℕ} (σ : I _⦋n + 1⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 2))
      (-((n + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + 1)) (by simp; omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarUnshiftedBoundary R D F σ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_full_rhs_sum]
  have hx : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).obj 0 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_castSucc R D F σ 0).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F σ 0)
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq (A := R) (D := RightModule R D) hx hy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiFullTerm R D F σ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarUnshiftedBoundaryTerm R D F σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiFullTerm_heq_boundaryTerm R D F σ)).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarUnshiftedBoundary_eq_sum_terms R D F σ).symm)

lemma dgCoherentBarBianchiData_full_rhs_heq_theta {n : ℕ} (σ : I _⦋n + 1⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 2))
      (-((n + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + 1)) (by simp; omega))
      (compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F ⟨n + 1, σ⟩) rfl) :=
  (dgCoherentBarBianchiData_full_rhs_heq_boundary R D F σ).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_comp_shiftedInclusion_positive R D F σ).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
