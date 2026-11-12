module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceChange

/-!
概要：指定した高次ホモトピー類を、固定した零ホモトピーとの差として実現する。
方針：差の球面と固定した零ホモトピーをホーンへ置き、もう一方を充填する。
規約：差の左端を固定した形と右端を固定した形の両方を用意する。
使われ方：Goerss–Jardine VIII §1。twisted 作用を零ホモトピーの選択変更で実現する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyDifference

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} {n : ℕ}
  {s : X.PtSimplex (n + 1) x}
  (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) (D : X.PtSimplex (n + 2) x)

/-- 差の球面と左端を指定したホーン。 -/
def realizationFace (j : Fin (n + 4)) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
  if j.val = n + 1 then D.map else if j.val = n + 2 then R.map else SSet.const x

omit [KanComplex X] in
/-- 指定した差の球面と零ホモトピーはホーン上で互換。 -/
lemma realizationCompatible :
    horn.IsCompatible (i := Fin.last (n + 3)) (fun j _ ↦ realizationFace R D j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 3 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 3 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [realizationFace]
  split_ifs <;> try simp only [PtSimplex.δ_map, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.ext_iff, Fin.val_last, Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 欠ける最後の面は元の球面の零ホモトピーとなる。 -/
lemma realization_output_face (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 3)) ≫
      (realizationCompatible R D).liftOfKanComplex =
      if j.val = n + 2 then s.map else SSet.const x := by
  rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
    (realizationCompatible R D).δ_liftOfKanComplex _ (Fin.castSucc_ne_last j)]
  simp only [realizationFace, Fin.val_castSucc]
  split_ifs <;> try simp only [PtSimplex.δ_map, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.ext_iff, Fin.val_last] at *
       first | contradiction | omega)

/-- 指定した球面の類を右側の零ホモトピーの選択で実現する。 -/
theorem exists_difference_simplex :
    ∃ S : PtSimplex.RelStruct .const s (Fin.last (n + 1)),
      difference R S = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk D := by
  let φ := (realizationCompatible R D).liftOfKanComplex
  let S : PtSimplex.RelStruct .const s (Fin.last (n + 1)) := {
    map := stdSimplex.δ (Fin.last (n + 3)) ≫ φ
    δ_castSucc_map := by rw [realization_output_face]; simp
    δ_succ_map := by rw [realization_output_face]; simp
    δ_map_of_lt j hj := by
      rw [realization_output_face, ite_eq_right (by
        have hjv : j.val < n + 1 := hj
        omega)]
    δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim }
  have hφ (j : Fin (n + 4)) (hj : j ≠ (Fin.last (n + 1)).castSucc.castSucc) :
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j := by
    by_cases hlast : j = Fin.last (n + 3)
    · subst j
      simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, S]
    · rw [(realizationCompatible R D).δ_liftOfKanComplex j hlast]
      have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
      simp only [realizationFace, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, ite_eq_right hj']
      have hlast' : j.val ≠ n + 3 := fun he ↦ hlast (Fin.ext he)
      rw [ite_eq_right hlast']
  refine ⟨S, ?_⟩
  rw [difference_eq_ofFiller R S φ hφ]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  change stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ φ = D.map
  rw [(realizationCompatible R D).δ_liftOfKanComplex _ (by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_last] at hh
    omega)]
  simp [realizationFace]

/-- 任意の高次の類は、固定した左端との差になる。 -/
theorem exists_difference (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) :
    ∃ S : PtSimplex.RelStruct .const s (Fin.last (n + 1)), difference R S = a := by
  obtain ⟨D, rfl⟩ := Quotient.exists_rep a
  exact exists_difference_simplex R D

/-- 任意の高次の類は、固定した右端との差になる。 -/
theorem exists_left_difference (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) :
    ∃ S : PtSimplex.RelStruct .const s (Fin.last (n + 1)), difference S R = a := by
  obtain ⟨S, hS⟩ := exists_difference R a⁻¹
  exact ⟨S, by rw [difference_inv, hS, inv_inv]⟩

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
