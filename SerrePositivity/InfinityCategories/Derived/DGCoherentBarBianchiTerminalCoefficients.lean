module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiFaces
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarSubsetCuts

/-!
概要：Bianchi の削除・右切断・全体成分を、元の bar の閉包含へ同定する。
方針：末端追加から先頭集合を回収し、厳密な部分単体ラベルの比較を適用する。
規約：全パラメーターと端点輸送を異種等号で保持する。
使われ方：末端への HA 右辺と θ の元の列の一項ごとの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))


private lemma barInclusion_heq_of_eq (s t : dgCoherentBarIndex I) (h : s = t) :
    HEq (dgCoherentBarShiftedInclusion R D F s) (dgCoherentBarShiftedInclusion R D F t) := by
  cases h
  rfl

lemma dgCoherentBarBianchiData_face_coefficient {n : ℕ} (σ : I _⦋n + 1⦌)
    (j : Fin (n + 2)) :
    let J := (Finset.univ : Finset (Fin (n + 2))).erase j
    ∀ (hJ : J.Nonempty),
    HEq ((dgCoherentBarBianchiData R D F σ).hom (DGNerve.PinchedHom.withLast J)
      (J.min' hJ).castSucc (Fin.last (n + 2)) (-(n : ℤ))
      (DGNerve.PinchedHom.two_withLast hJ) (DGNerve.PinchedHom.min_withLast hJ _)
      (DGNerve.PinchedHom.max_withLast J _) (by
        rw [DGNerve.PinchedHom.card_withLast]; simp [J]; omega))
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarFace σ j)) := by
  intro J hJ
  have hc : J.card = n + 1 := by simp [J]
  have hl := (dgCoherentBarBianchiLabel_withLast σ J n hc hJ).trans
    (dgCoherentBarSubsetLabel_face σ j)
  have hh := dgCoherentBarBianchiData_last_hom_heq R D F σ
    (DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (-(n : ℤ))
    (DGNerve.PinchedHom.two_withLast hJ) (DGNerve.PinchedHom.min_withLast hJ _)
    (DGNerve.PinchedHom.max_withLast J _) (by
      rw [DGNerve.PinchedHom.card_withLast, hc]; omega)
  exact hh.trans (barInclusion_heq_of_eq R D F _ _ hl)

lemma dgCoherentBarBianchiData_tail_coefficient {n : ℕ} (σ : I _⦋n⦌)
    (j : Fin (n + 1)) :
    let J := (Finset.univ : Finset (Fin (n + 1))).filter (j ≤ ·)
    ∀ (hJ : J.Nonempty),
    HEq ((dgCoherentBarBianchiData R D F σ).hom (DGNerve.PinchedHom.withLast J)
      (J.min' hJ).castSucc (Fin.last (n + 1)) (-((n - j.val : ℕ) : ℤ))
      (DGNerve.PinchedHom.two_withLast hJ) (DGNerve.PinchedHom.min_withLast hJ _)
      (DGNerve.PinchedHom.max_withLast J _) (by
        rw [DGNerve.PinchedHom.card_withLast, dgCoherentBarTail_card]; omega))
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarTail σ j.val (by omega))) := by
  intro J hJ
  have hc : J.card = n - j.val + 1 := dgCoherentBarTail_card n j
  have hl := (dgCoherentBarBianchiLabel_withLast σ J (n - j.val) hc hJ).trans
    (dgCoherentBarSubsetLabel_tail σ j)
  have hh := dgCoherentBarBianchiData_last_hom_heq R D F σ
    (DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (-((n - j.val : ℕ) : ℤ))
    (DGNerve.PinchedHom.two_withLast hJ) (DGNerve.PinchedHom.min_withLast hJ _)
    (DGNerve.PinchedHom.max_withLast J _) (by
      rw [DGNerve.PinchedHom.card_withLast, hc]; omega)
  exact hh.trans (barInclusion_heq_of_eq R D F _ _ hl)


lemma dgCoherentBarBianchiData_full_coefficient {n : ℕ} (σ : I _⦋n⦌)
    (hJ : (Finset.univ : Finset (Fin (n + 1))).Nonempty) :
    HEq ((dgCoherentBarBianchiData R D F σ).hom (DGNerve.PinchedHom.withLast Finset.univ)
      (Finset.univ.min' hJ).castSucc (Fin.last (n + 1)) (-(n : ℤ))
      (DGNerve.PinchedHom.two_withLast hJ) (DGNerve.PinchedHom.min_withLast hJ _)
      (DGNerve.PinchedHom.max_withLast Finset.univ _) (by
        rw [DGNerve.PinchedHom.card_withLast]; simp; omega))
      (dgCoherentBarShiftedInclusion R D F ⟨n, σ⟩) := by
  have hl := (dgCoherentBarBianchiLabel_withLast σ Finset.univ n (by simp) hJ).trans
    (dgCoherentBarSubsetLabel_univ σ)
  have hh := dgCoherentBarBianchiData_last_hom_heq R D F σ
    (DGNerve.PinchedHom.withLast Finset.univ) (Finset.univ.min' hJ).castSucc (-(n : ℤ))
    (DGNerve.PinchedHom.two_withLast hJ) (DGNerve.PinchedHom.min_withLast hJ _)
    (DGNerve.PinchedHom.max_withLast Finset.univ _) (by
      rw [DGNerve.PinchedHom.card_withLast]; simp; omega)
  exact hh.trans (barInclusion_heq_of_eq R D F _ _ hl)

end SerrePositivity.InfinityCategories
