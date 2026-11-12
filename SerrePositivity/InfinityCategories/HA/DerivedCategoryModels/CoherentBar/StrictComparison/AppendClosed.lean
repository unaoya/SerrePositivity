module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendColumn
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationColumns

/-!
概要：局所縮約の末尾付加係数は内部微分について閉じ、最後の頂点の重複で零になる。
方針：shift 単位の閉性を端点輸送し、退化ラベルの正規化射影消滅を使う。
規約：bar 微分による縮約恒等式は後続で検証する。
使われ方：filtered strict bar の局所縮約の各列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) {n : ℕ}

set_option maxHeartbeats 800000 in
-- The endpoint equality also transports the selected enriched Hom complex.
lemma dgStrictAppendBlock_d (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
          ⟨n + 1, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendSimplex s b hb⟩))).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendBlock R D F s b hb) = 0 := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n, s⟩
  let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
    ⟨n + 1, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendSimplex s b hb⟩
  have hy : _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) N = _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M :=
    congrArg (shiftModule ((n + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendSource R D F s b hb)
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D)
    (x := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) N)
    (x' := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M) (y' := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M)
    rfl hy rfl _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendBlock_heq R D F s b hb)
  have hc := _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_unit_d R D (n : ℤ) ((n + 1 : ℕ) : ℤ) M (-1) (by omega)
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
    (x := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) N)
    (x' := _root_.SerrePositivity.DifferentialGraded.shiftModule (n : ℤ) M) (y' := _root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ) M)
    (k := (0 : ℤ)) (l := (0 : ℤ)) rfl hy rfl
  exact eq_of_heq ((hd.trans (heq_of_eq hc)).trans hz.symm)

lemma dgStrictAppendColumn_eq_zero_of_last_eq (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) (he : s.obj (Fin.last n) = b) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendColumn R D F s b hb = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendColumn
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_degenerate R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
    ⟨⟨n + 1, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendSimplex s b hb⟩,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendSimplex_degenerate_of_last_eq s b hb he⟩]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_zero R D (-1) _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
