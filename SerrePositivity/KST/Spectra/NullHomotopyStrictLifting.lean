module

public import SerrePositivity.KST.Spectra.NullDifferenceZeroFiller
public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceNaturality

/-!
概要：Kan fibration の下で零の差を持つ零ホモトピーの射影を厳密に調整する。
方針：底の定数面つき充填を、最後の面を固定する相対ホーンで持ち上げる。
規約：球面代表を変えず、元の零ホモトピーとの差の零性も保つ。
使われ方：Goerss–Jardine VIII §1。塔で整合する零ホモトピーの逐次構成。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyStrictLifting

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NullHomotopyDifference

variable {E B : SSet.{u}} {e : E _⦋0⦌} {n : ℕ} {s : E.PtSimplex (n + 1) e}

/-- 最後の面だけを固定した持ち上げホーン。 -/
def face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) (j : Fin (n + 4)) :
    (Δ[n + 2] : SSet.{u}) ⟶ E := if j.val = n + 3 then R.map else SSet.const e

/-- 最後の面の他の面は全て定数なのでホーンは互換。 -/
lemma compatible (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    horn.IsCompatible (i := (Fin.last (n + 2)).castSucc) (fun j _ ↦ face R j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 2 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.ext_iff, Fin.val_last, Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 持ち上げホーンの欠ける面は元の球面の零ホモトピー。 -/
lemma output_face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ E)
    (hφ : ∀ j, j ≠ (Fin.last (n + 2)).castSucc → stdSimplex.δ j ≫ φ = face R j)
    (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 2)).castSucc ≫ φ =
      if j.val = n + 2 then s.map else SSet.const e := by
  by_cases hj : j ≤ (Fin.last (n + 1)).castSucc
  · have he : (Fin.last (n + 2)).castSucc = ((Fin.last (n + 1)).castSucc).succ := by
      apply Fin.ext; rfl
    rw [he, stdSimplex.δ_comp_δ_assoc hj, hφ _ (by
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      have hjv : j.val ≤ n + 1 := hj
      omega)]
    have hjv : j.val ≤ n + 1 := hj
    simp only [face, Fin.val_castSucc]
    rw [ite_eq_right (by omega), comp_const, ite_eq_right (by omega)]
  · have hjlast : j = Fin.last (n + 2) := by
      apply Fin.ext
      have hjb := j.isLt
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last] at hj ⊢
      omega
    subst j
    rw [← stdSimplex.δ_comp_δ_assoc (show Fin.last (n + 2) ≤ Fin.last (n + 2) from le_rfl),
      hφ _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ] at hh
        omega)]
    simp only [face, Fin.val_succ, Fin.val_last, ite_true]
    simpa only [Fin.succ_last] using R.δ_succ_map

/-- 指定した射影へ零ホモトピーを調整し、upstairs の差の零性を保つ。 -/
theorem exists_adjust (p : E ⟶ B) [Fibration p] [KanComplex E] [KanComplex B]
    (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (T : PtSimplex.RelStruct .const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) (Fin.last (n + 1)))
    (he : difference T (mapNull p rfl R) = 1) :
    ∃ U : PtSimplex.RelStruct .const s (Fin.last (n + 1)),
      U.map ≫ p = T.map ∧ difference U R = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_zero_filler T (mapNull p rfl R) he
  have hcomm (j : Fin (n + 4)) (hj : j ≠ (Fin.last (n + 2)).castSucc) :
      face R j ≫ p = stdSimplex.δ j ≫ ψ := by
    rw [hψ]
    have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
    simp only [face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, ite_eq_right hj']
    split_ifs <;> first | rfl | exact const_comp _ _
  obtain ⟨φ, hφ, hp⟩ := (compatible R).exists_lift p ψ hcomm
  let U : PtSimplex.RelStruct .const s (Fin.last (n + 1)) := {
    map := stdSimplex.δ (Fin.last (n + 2)).castSucc ≫ φ
    δ_castSucc_map := by rw [output_face R φ hφ]; simp
    δ_succ_map := by rw [output_face R φ hφ]; simp
    δ_map_of_lt j hj := by
      rw [output_face R φ hφ, ite_eq_right (by
        have hjv : j.val < n + 1 := hj
        omega)]
    δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim }
  refine ⟨U, ?_, ?_⟩
  · change (stdSimplex.δ (Fin.last (n + 2)).castSucc ≫ φ) ≫ p = T.map
    rw [Category.assoc, hp, hψ]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  · apply difference_eq_one_of_zero_filler U R φ
    intro j
    by_cases hj : j.val = n + 2
    · have hj' : j = (Fin.last (n + 2)).castSucc := Fin.ext hj
      subst j
      simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, Fin.val_castSucc, Fin.val_last, ite_true]
      rfl
    · rw [hφ _ (fun he ↦ hj (congrArg Fin.val he))]
      simp only [face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, ite_eq_right hj]

end
end SerrePositivity.KST.Spectra.NullHomotopyStrictLifting
