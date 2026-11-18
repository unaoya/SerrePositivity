module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DegenerateDeletionNeighbors
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OtherFaceZeroTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NonSurjectiveZeroTerms

/-!
模型。文献の定義との比較は後で
# 退化した水平削除語の元の境界項は零

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
削除した区間の両隣の水平辺を読み、残る別の色の因子の正規化の消滅を使う。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C208：退化した水平削除では、削除しない別の色の面に二つの同じ頂点が残る。 -/
lemma other_face_not_mono_horizontal_degenerate {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalVertex s k)
    (hdeg : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal k))) :
    ∃ c : Fin r, c ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k ∧ ¬Mono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v c) := by
  obtain ⟨i, j, hia, haj, hcolor⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erased_word_degenerate_neighbors v (s.horizontal k) hdeg
  have hk0 : 0 < k.val := by
    by_contra h
    have he : k = 0 := by
      apply Fin.ext
      change k.val = 0
      omega
    rw [he, s.horizontal_endpoints.1] at hia
    simp only [Fin.val_zero] at hia
    omega
  have hkN : k.val < m + 1 + q := by
    by_contra h
    have he : k = Fin.last (m + 1 + q) := by
      apply Fin.ext
      change k.val = m + 1 + q
      have := k.isLt
      omega
    rw [he, s.horizontal_endpoints.2] at haj
    have hj := j.isLt
    simp only [Fin.val_last] at haj
    omega
  let l : Fin (m + 1 + q) := ⟨k.val - 1, by omega⟩
  let e : Fin (m + 1 + q) := ⟨k.val, hkN⟩
  have hl : l.succ = k := Fin.ext (by change k.val - 1 + 1 = k.val; omega)
  have he : e.castSucc = k := Fin.ext rfl
  obtain ⟨hlh, hlv⟩ := s.step_of_mem l (hk.1 l hl)
  obtain ⟨heh, hev⟩ := s.step_of_mem e (hk.2 e he)
  rw [hl] at hlh hlv
  rw [he] at heh hev
  have hi : s.horizontal l.castSucc = i := Fin.ext (by omega)
  have hj : s.horizontal e.succ = j := Fin.ext (by omega)
  have hne : l.castSucc ≠ e.succ := by
    intro h
    have hval := congrArg (fun z : Fin (m + 1 + q + 1) => z.val) h
    change k.val - 1 = k.val + 1 at hval
    omega
  refine ⟨v.val i, v.nondegenerate i (s.horizontal k) hia, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face_not_mono_of_repeated_color s v (v.val i) l.castSucc e.succ
  · change v.val (s.horizontal l.castSucc) = v.val i
    rw [hi]
  · change v.val (s.horizontal e.succ) = v.val i
    rw [hj]
    exact hcolor.symm
  · exact hne
  · exact hlv.symm.trans hev.symm

/-- C209：退化な削除の元の境界項は、残る別の色の因子の正規化により零。 -/
lemma outputBoundaryTerm_horizontal_degenerate {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalVertex s k)
    (hdeg : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal k)))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) j x = 0 := by
  obtain ⟨c, hc, hm⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.other_face_not_mono_horizontal_degenerate s v k hk hdeg
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_eq_zero_of_other_face A S s v _ j c hc hm x

/-- C210：非全射または隣接退化で無効な水平削除の元の境界項は零。 -/
lemma outputBoundaryTerm_horizontal_invalid {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalVertex s k)
    (hinvalid : ¬(Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal k)) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal k))))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) j x = 0 := by
  by_cases hs : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal k))
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_horizontal_degenerate A S s v k hk
      (fun hn => hinvalid ⟨hs, hn⟩) j x
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_horizontal_not_surjective A S s v k hk hs j x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
