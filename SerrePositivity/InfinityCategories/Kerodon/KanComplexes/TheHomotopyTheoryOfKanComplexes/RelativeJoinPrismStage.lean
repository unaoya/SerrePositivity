module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPrismPenultimate
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismShuffleVertices
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：切替位置の順に最大単体を加える prism の有限段階。
方針：Z(0) に切替位置が r 未満の最大単体を加える。
規約：段階を自然数で添字付け、m 段階で既存の Z(m) に一致させる。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の内側ホーンによる帰納。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：prism の最大単体を r 個目まで加えた部分複体。
方針：切替位置が r 未満の生成単体の和と初期部分の和を取る。
規約：r=0 では初期部分だけ、r=m では Z(m)。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、prism の有限分解の添字。 -/
@[kerodon 00TH]
noncomputable def relativeJoinPrismStage (m r : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m ⊔
    ⨆ k : {k : Fin (m + 1) // k.val < r},
      Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k.val)

/-- 概要：prism の零段階は境界と終端からなる初期部分。
方針：零より小さい切替位置が存在しないことを使う。
規約：標準単体の次元 m は任意。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、有限帰納の基底。 -/
lemma relativeJoinPrismStage_zero (m : ℕ) :
    relativeJoinPrismStage.{u} m 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m := by
  simp [relativeJoinPrismStage]

/-- 概要：prism の m 段階は最後の最大単体を除いた Z(m)。
方針：切替位置の値が m 未満である条件を Fin の最後の頂点との比較へ直す。
規約：既存の境界への因子化と同じ部分複体である。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、有限分解と境界への射との接続。 -/
lemma relativeJoinPrismStage_penultimate (m : ℕ) :
    relativeJoinPrismStage.{u} m m = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimate m := rfl

/-- 概要：prism の段階は添字に関して単調。
方針：生成単体の切替位置の不等式を推移させる。
規約：自然数の全ての段階で単調性を主張する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、段階間の標準包含。 -/
lemma relativeJoinPrismStage_monotone (m : ℕ) :
    Monotone (relativeJoinPrismStage.{u} m) := by
  intro r s hrs
  apply sup_le_sup_left
  apply iSup_le
  intro k
  exact le_iSup_of_le ⟨k.val, lt_of_lt_of_le k.property hrs⟩ le_rfl

/-- 概要：r 段階から次へ進むときは切替位置 r の最大単体を一つ加える。
方針：r+1 未満の切替位置を r 未満と r 自身に分ける。
規約：追加する切替位置 k の値が r である形で記述する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、単一ホーンの pushout への還元。 -/
lemma relativeJoinPrismStage_succ (m : ℕ) (k : Fin (m + 1)) :
    relativeJoinPrismStage.{u} m (k.val + 1) =
      relativeJoinPrismStage m k.val ⊔ Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k) := by
  apply le_antisymm
  · apply sup_le
    · exact le_sup_of_le_left le_sup_left
    · apply iSup_le
      intro j
      by_cases hj : j.val.val < k.val
      · exact le_sup_of_le_left (le_sup_of_le_right
          (le_iSup (fun j : {j : Fin (m + 1) // j.val < k.val} ↦
            Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j.val)) ⟨j.val, hj⟩))
      · have he : j.val = k := Fin.ext (by omega)
        simpa only [he] using (le_sup_right :
          Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k) ≤
            relativeJoinPrismStage m k.val ⊔ Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k))
  · apply sup_le
    · exact relativeJoinPrismStage_monotone m (Nat.le_succ k.val)
    · exact le_sup_of_le_right (le_iSup (fun j : {j : Fin (m + 1) // j.val < k.val + 1} ↦
        Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j.val)) ⟨k, Nat.lt_succ_self k.val⟩)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
