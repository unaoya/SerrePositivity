module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismHornPreimage

/-!
概要：prism の最大単体の切替の二面以外の面が境界 prism に入ること。
方針：係数の重複する二頂点以外は一意であるため、面を取るとその係数頂点が欠ける。
規約：除外する面の番号は k と k+1。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、ホーンから既存の段階への包含。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：切替の二頂点以外の係数の逆像は一意。
方針：退化の頂点の式を切替の前後で計算する。
規約：係数が重複する k 番目と k+1 番目を除外する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、面で欠ける係数頂点の判定。 -/
lemma relativeJoinPrismShuffle_coefficient_fiber_singleton (m : ℕ) (k : Fin (m + 1))
    (i j : Fin (m + 2)) (hi₀ : i ≠ k.castSucc) (hi₁ : i ≠ k.succ)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 j =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 i) : j = i := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_coefficient_val.{u} m k j,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_coefficient_val.{u} m k i] at hv
  have h₀ : i.val ≠ k.val := fun he ↦ hi₀ (Fin.ext he)
  have h₁ : i.val ≠ k.val + 1 := fun he ↦ hi₁ (Fin.ext he)
  change (if j.val ≤ k.val then j.val else j.val - 1) =
    (if i.val ≤ k.val then i.val else i.val - 1) at hv
  split_ifs at hv <;> omega

/-- 概要：切替の二面以外の面の係数は境界に入る。
方針：削除した頂点の係数の逆像の一意性から、その係数が面で欠けることを示す。
規約：係数側の境界は標準 m 単体の境界。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、prism の境界に既に含まれる面。 -/
lemma relativeJoinPrismShuffle_face_coefficient_mem_boundary (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) (hi₀ : i ≠ k.castSucc) (hi₁ : i ≠ k.succ) :
    (((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k)).2 ∈
      (boundary m).obj (Opposite.op ⦋m⦌) := by
  apply (mem_boundary_iff_notMem_range _).mpr
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 i, ?_⟩
  rintro ⟨j, hj⟩
  have he : i.succAbove j = i :=
    relativeJoinPrismShuffle_coefficient_fiber_singleton.{u} m k i (i.succAbove j) hi₀ hi₁ hj
  exact Fin.succAbove_ne i j he

/-- 概要：切替の二面以外の面は初期の境界 prism に含まれる。
方針：面の係数を境界の単体に持ち上げ、区間の成分はそのまま使う。
規約：初期部分は終端も含むが、この面では境界 prism の部分だけを使う。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、ホーンの面から初期部分への射。 -/
lemma relativeJoinPrismShuffle_face_mem_initial (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) (hi₀ : i ≠ k.castSucc) (hi₁ : i ≠ k.succ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).obj (Opposite.op ⦋m⦌) := by
  apply Or.inl
  exact ⟨⟨_, ⟨_, relativeJoinPrismShuffle_face_coefficient_mem_boundary m k i hi₀ hi₁⟩⟩, rfl⟩

/-- 概要：隣接する最大単体の切替位置の面は同じ単体である。
方針：Mathlib の codimOneSimplex による二つの面の式を照合する。
規約：切替位置 j+1 の j+1 番目の面と、位置 j の j+1 番目の面を比較する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、前のセルと共有する面の同定。 -/
lemma relativeJoinPrismShuffle_shared_face (m : ℕ) (j : Fin m) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ j.succ.castSucc
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m j.succ) =
      ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ j.castSucc.succ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m j.castSucc) := by
  have he : ((Δ[m] : SSet.{u}) ⊗ Δ[1]).δ j.succ.castSucc
        (prodStdSimplex₁.nonDegenerateEquiv j.succ).val =
      ((Δ[m] : SSet.{u}) ⊗ Δ[1]).δ j.castSucc.succ
        (prodStdSimplex₁.nonDegenerateEquiv j.castSucc).val := by
    rw [prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv,
      prodStdSimplex₁.δ_succ_nonDegenerateEquiv, Fin.succ_castSucc]
  exact congrArg Prod.swap he

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
