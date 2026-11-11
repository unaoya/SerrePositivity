module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PrismCellPushout
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：prism の各段階をホーンの pushout として構成する。
方針：逆像のホーンとの同定、最大単体の単射性、次段階の生成表示を使う。
規約：最後より前の切替位置ではホーンが内側となる。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の inner anodyne 分解。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：最大単体の characteristic map の像はその単体が生成する部分複体。
方針：Yoneda の対応と単体の引き戻しによる生成表示を照合する。
規約：区間を左因子とする prism の表示を使う。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、次段階の像による被覆。 -/
lemma relativeJoinPrismShuffle_range (m : ℕ) (k : Fin (m + 1)) :
    Subcomplex.range (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k)) =
      Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k) := by
  ext n z
  rw [Subcomplex.mem_ofSimplex_obj_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨stdSimplex.objEquiv a, ha⟩
  · rintro ⟨f, hf⟩
    exact ⟨stdSimplex.objEquiv.symm f, hf⟩

/-- 概要：セルのホーンを既存の prism の段階へ写す。
方針：逆像のホーンとの同定を用いて characteristic map を制限する。
規約：切替位置 k のホーンの欠ける面は k+1。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、ホーンを貼り付ける射。 -/
noncomputable def relativeJoinPrismCellHorn (m : ℕ) (k : Fin (m + 1)) :
    (horn (m + 1) k.succ : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val :=
  Subcomplex.lift ((horn (m + 1) k.succ).ι ≫
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k)) (by
      intro n z hz
      obtain ⟨a, rfl⟩ := hz
      exact (congrArg (fun P ↦ a.val ∈ P.obj n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_preimage_shuffle_eq_horn.{u} m k)).mpr a.property)

/-- 概要：最大単体の characteristic map を次の prism の段階へ写す。
方針：次段階がこの単体を生成単体として含むことを使う。
規約：係数の次数は m+1。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、貼り付けるセルの射。 -/
noncomputable def relativeJoinPrismCellSimplex (m : ℕ) (k : Fin (m + 1)) :
    (Δ[m + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m (k.val + 1) :=
  Subcomplex.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k)) (by
    rw [relativeJoinPrismShuffle_range, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_succ]
    exact le_sup_right)

/-- 概要：prism の一段の追加は k+1 番目のホーンの pushout。
方針：単射のセルの貼り合わせ判定に逆像の等式と次段階の生成表示を適用する。
規約：最後の切替位置も含む通常の pushout の等式。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、有限個のホーンの合成。 -/
@[kerodon 00TH]
lemma relativeJoinPrismCell_isPushout (m : ℕ) (k : Fin (m + 1)) :
    IsPushout (horn (m + 1) k.succ).ι (relativeJoinPrismCellHorn m k)
      (relativeJoinPrismCellSimplex m k)
      (Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_monotone m (Nat.le_succ k.val))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isPushout_prism_mono_cell
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m (k.val + 1))
    (horn (m + 1) k.succ) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k))
    (by rw [relativeJoinPrismShuffle_range, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_succ])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_preimage_shuffle_eq_horn m k).symm
  · exact Subcomplex.lift_ι _ _
  · exact Subcomplex.lift_ι _ _

/-- 概要：最後より前の prism の一段の追加は inner anodyne。
方針：pushout で貼るホーンの番号が零でも最後でもないことを使う。
規約：モデル構造を使わず inner fibration に対する左持ち上げ性を結論する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の Z(0) から Z(m) への合成。 -/
lemma innerAnodyneExtensions_relativeJoinPrismStage_step (m : ℕ) (k : Fin (m + 1))
    (hk : k < Fin.last m) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_monotone.{u} m (Nat.le_succ k.val))) := by
  have hm : NeZero m := ⟨by intro he; subst m; exact (not_lt_of_ge (Fin.zero_le k)) hk⟩
  have hh : innerAnodyneExtensions (horn (m + 1) k.succ).ι :=
    .horn_ι (by simp) (by change k.val + 1 < m + 1; exact Nat.add_lt_add_right hk 1)
  exact innerAnodyneExtensions.of_isPushout (relativeJoinPrismCell_isPushout m k).flip hh

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
