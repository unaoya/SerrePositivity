module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismCell
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：prism の有限段階の全体の被覆と最後のセルの分離。
方針：Mathlib の最大非退化単体の列挙を因子の交換で移し、全体の生成判定を使う。
規約：m+1 段階で prism 全体、m 段階で Z(m) を得る。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の比較の交わりの計算。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：全ての最大単体を追加した prism の段階は全体。
方針：非退化な最大次元の単体を列挙し、それぞれが生成部分に入ることを示す。
規約：区間を左因子とする表示に列挙を移す。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、prism の有限分解の終点。 -/
@[kerodon 00TH]
lemma relativeJoinPrismStage_top (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage.{u} m (m + 1) = ⊤ := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ (by omega : 1 + m = m + 1)]
  intro z hz
  let z' := (nonDegenerateEquivOfIso (β_ (Δ[1] : SSet.{u}) Δ[m])) ⟨z, hz⟩
  obtain ⟨k, hk⟩ := prodStdSimplex₁.nonDegenerateEquiv.surjective z'
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k = z :=
    congrArg (fun w : ((Δ[m] : SSet.{u}) ⊗ Δ[1]).nonDegenerate (m + 1) ↦
      Prod.swap w.val) hk
  rw [← he]
  have hle : Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k) ≤
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m (m + 1) :=
    le_sup_of_le_right (le_iSup
      (fun k : {k : Fin (m + 1) // k.val < m + 1} ↦
        Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k.val)) ⟨k, k.isLt⟩)
  exact hle _ (Subcomplex.mem_ofSimplex_obj _)

/-- 概要：prism は Z(m) と最後の最大単体で覆われる。
方針：最後の段階の一段の生成表示を全体の被覆と比較する。
規約：二つの部分複体の和としての等式。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後のセルでの逆像の検査への還元。 -/
lemma relativeJoinPrismPenultimate_sup_last (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimate.{u} m ⊔
        Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m (Fin.last m)) = ⊤ := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_penultimate]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_succ.{u} m (Fin.last m)).symm.trans
    (relativeJoinPrismStage_top m)

/-- 概要：prism の任意の単体は Z(m) に入るか最後の最大単体から来る。
方針：部分複体の和による被覆を各次数で評価する。
規約：全ての次数 d の単体に適用する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界の逆像を最後のセルだけで検査する。 -/
lemma relativeJoinPrismPenultimate_or_last (m d : ℕ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌) :
    z ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimate m).obj (Opposite.op ⦋d⦌) ∨
      ∃ a : (Δ[m + 1] : SSet.{u}) _⦋d⦌,
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m (Fin.last m))).app
          (Opposite.op ⦋d⦌) a = z := by
  have h : z ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimate.{u} m ⊔
      Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m (Fin.last m))).obj
        (Opposite.op ⦋d⦌) := by rw [relativeJoinPrismPenultimate_sup_last]; trivial
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_range] at h
    exact h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
