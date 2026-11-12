module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismBoundaryFaces

/-!
概要：prism の一段を貼る際の既存部分の逆像とホーンの同定。
方針：境界に入る面と前の最大単体と共有する面を合わせ、既存の上界と比較する。
規約：切替位置 k のセルで欠ける面は k+1 番目。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） のホーンの pushout。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：最初の最大単体の零番目の面は終端に入る。
方針：零番目の面は時刻が全て一である codimOneSimplex と同定する。
規約：係数の標準単体の次元 m は任意。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、最初のホーンの終端の面。 -/
lemma relativeJoinPrismShuffle_zero_face_mem_initial (m : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m 0) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).obj (Opposite.op ⦋m⦌) := by
  have he := congrArg Prod.swap
    (prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv.{u} (0 : Fin (m + 1)))
  change ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m 0) =
    ((prodStdSimplex₁.codimOneSimplex 0).val.2,
      (prodStdSimplex₁.codimOneSimplex 0).val.1) at he
  rw [he]
  apply Or.inr
  refine ⟨(prodStdSimplex₁.codimOneSimplex 0).val.1, ?_⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    change (1 : Fin 2) = stdSimplex.objMk₁.{u} 0 i
    exact (stdSimplex.objMk₁_of_le_castSucc.{u} 0 i (Fin.zero_le _)).symm
  · rfl

/-- 概要：切替位置 k の k 番目の面はセルを加える前の段階に含まれる。
方針：最初のセルでは終端、それ以降では一つ前のセルとの共有面を使う。
規約：欠ける面 k+1 の直前の面を扱う。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、ホーンの残る一面の所属。 -/
lemma relativeJoinPrismShuffle_switch_face_mem_stage (m : ℕ) (k : Fin (m + 1)) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ k.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val).obj (Opposite.op ⦋m⦌) := by
  by_cases hk : k = 0
  · subst k
    have hle : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial.{u} m ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m 0 := le_sup_left
    exact hle _ (relativeJoinPrismShuffle_zero_face_mem_initial m)
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_shared_face]
    have hle : Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j.castSucc) ≤
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m j.succ.val :=
      le_sup_of_le_right (le_iSup (fun k : {k : Fin (m + 1) // k.val < j.succ.val} ↦
        Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k.val)) ⟨j.castSucc, by simp⟩)
    apply hle
    exact (Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m j.castSucc)).map
      (SimplexCategory.δ j.castSucc.succ).op (Subcomplex.mem_ofSimplex_obj _)

/-- 概要：欠ける k+1 番目以外の全ての面は既存の段階に含まれる。
方針：切替の面は共有面、それ以外は初期の境界 prism を使う。
規約：最後のセルも含む全ての切替位置で成立する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、ホーン全体の既存部分への因子化。 -/
lemma relativeJoinPrismShuffle_face_mem_stage (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) (hi : i ≠ k.succ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val).obj (Opposite.op ⦋m⦌) := by
  by_cases hi₀ : i = k.castSucc
  · subst i
    exact relativeJoinPrismShuffle_switch_face_mem_stage m k
  · have hle : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial.{u} m ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val := le_sup_left
    exact hle _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismShuffle_face_mem_initial m k i hi₀ hi)

/-- 概要：セル k の characteristic map に沿う既存の段階の逆像は k+1 番目のホーン。
方針：ホーンを全ての残る面の和に分解し、面の所属と既存の上界を合わせる。
規約：この等式から各段階をホーンの貼り合わせとして扱う。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の prism の分解。 -/
lemma relativeJoinPrismStage_preimage_shuffle_eq_horn (m : ℕ) (k : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage m k.val).preimage
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k)) = horn (m + 1) k.succ := by
  apply le_antisymm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_preimage_shuffle_le_horn m k)
  rw [← Subcomplex.image_le_iff, horn_eq_iSup, Subcomplex.image_iSup]
  apply iSup_le
  intro i
  rw [stdSimplex.face_singleton_compl, Subcomplex.image_ofSimplex,
    Subcomplex.ofSimplex_le_iff]
  exact relativeJoinPrismShuffle_face_mem_stage m k i.val i.property

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
