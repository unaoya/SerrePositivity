module

public import SerrePositivity.InfinityCategories.DoldKanComparison.DegenerateEvaluation

/-!
# 薄い圏の nerve の繰り返す頂点の評価

概要：薄い圏の nerve の隣接頂点が等しければ、標準 Hom での最上位評価は零である。
方針：頂点を一つ削除して退化で戻した単体と一致することを対象上で証明する。
規約：既存の圏構造を使い、部分順序の instance は追加しない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の native Path の退化旗の消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：薄い圏の nerve の隣接頂点の反復は最上位評価を零にする。
方針：反復頂点を削除してから退化させて元の単体を復元し、退化単体の評価の零を使う。
規約：射の一意性は薄さから得る。
使われ方：Kerodon 2.5.9 の Path の像で潰れた旗の評価。 -/
lemma standardTopEval_thin_nerve_repeat_zero {P : Type u} [Category.{u} P]
    [Quiver.IsThin P] {n : ℕ} (φ : nerve P ⟶ standardHomSpace (R := R) x y)
    (s : (nerve P) _⦋n⦌) (i : Fin n)
    (hi : s.obj i.castSucc = s.obj i.succ) :
    standardTopEval (R := R) x y n (φ.app _ s) = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      apply standardTopEval_map_degenerate_zero
      rw [SSet.degenerate_eq_iUnion_range_σ]
      apply Set.mem_iUnion.mpr
      refine ⟨i, (nerve P).δ i.castSucc s, ?_⟩
      refine CategoryTheory.Functor.ext (fun j ↦ ?_) (by intros; apply Subsingleton.elim)
      rw [nerve.σ_obj, nerve.δ_obj]
      by_cases h₁ : i.castSucc < j
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
        rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.pred_succ,
          Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
      · simp only [not_lt] at h₁
        grind [→ Fin.succAbove_of_castSucc_lt, → Fin.predAbove_of_le_castSucc,
          Fin.castSucc_castPred, Fin.castPred_castSucc, Fin.succAbove_castSucc_self,
          → LE.le.lt_or_eq]

end SerrePositivity.InfinityCategories.DoldKanComparison
