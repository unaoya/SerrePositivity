module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendColumn
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationColumns

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D) {n : ℕ}

set_option maxHeartbeats 800000 in
-- The endpoint equality also transports the selected enriched Hom complex.
lemma dgStrictAppendBlock_d (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)
          ⟨n + 1, dgStrictAppendSimplex s b hb⟩))).d (-1) 0
      (dgStrictAppendBlock R D F s b hb) = 0 := by
  let M := dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩
  let N := dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F)
    ⟨n + 1, dgStrictAppendSimplex s b hb⟩
  have hy : shiftModule ((n + 1 : ℕ) : ℤ) N = shiftModule ((n + 1 : ℕ) : ℤ) M :=
    congrArg (shiftModule ((n + 1 : ℕ) : ℤ)) (dgStrictAppendSource R D F s b hb)
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D)
    (x := shiftModule (n : ℤ) M) (y := shiftModule ((n + 1 : ℕ) : ℤ) N)
    (x' := shiftModule (n : ℤ) M) (y' := shiftModule ((n + 1 : ℕ) : ℤ) M)
    rfl hy rfl _ _ (dgStrictAppendBlock_heq R D F s b hb)
  have hc := moduleHomShiftBlock_unit_d R D (n : ℤ) ((n + 1 : ℕ) : ℤ) M (-1) (by omega)
  have hz := gradedHom_zero_heq (A := R) (D := RightModule R D)
    (x := shiftModule (n : ℤ) M) (y := shiftModule ((n + 1 : ℕ) : ℤ) N)
    (x' := shiftModule (n : ℤ) M) (y' := shiftModule ((n + 1 : ℕ) : ℤ) M)
    (k := (0 : ℤ)) (l := (0 : ℤ)) rfl hy rfl
  exact eq_of_heq ((hd.trans (heq_of_eq hc)).trans hz.symm)

lemma dgStrictAppendColumn_eq_zero_of_last_eq (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) (he : s.obj (Fin.last n) = b) :
    dgStrictAppendColumn R D F s b hb = 0 := by
  unfold dgStrictAppendColumn
  rw [dgCoherentBarNormalizedProjection_ι_degenerate R D
    (dgCoherentBarStrictDiagram R D F)
    ⟨⟨n + 1, dgStrictAppendSimplex s b hb⟩,
      dgStrictAppendSimplex_degenerate_of_last_eq s b hb he⟩]
  exact dgCoherentBarHom_postcompose_zero R D (-1) _

end SerrePositivity.InfinityCategories
