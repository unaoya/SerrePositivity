module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceClass

/-!
概要：三つの零ホモトピーの差の合成則。
方針：三つの差の充填を一つ高いホーンの最後の三面へ貼り、欠ける面を積の充填と読む。
規約：MulStruct の面の順序に合わせ、ST の差と RS の差の積を RT の差と比較する。
使われ方：Goerss–Jardine VIII §1。lim¹ の代表の選択変更。
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

/-- 差の充填の全ての面。欠けていた面には差の球面が現れる。 -/
lemma filler_face (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex =
      if j.val = n + 1 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S).map else _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j := by
  by_cases hj : j.val = n + 1
  · have he : j = (Fin.last (n + 1)).castSucc.castSucc := Fin.ext hj
    subst j
    rw [ite_eq_left hj]
    rfl
  · rw [ite_eq_right hj]
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).δ_liftOfKanComplex j (fun he ↦ hj (congrArg Fin.val he))

/-- 三つの差の充填を最後の三面に置く。 -/
def compositionFace (R S T : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n + 2 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex else
    if j.val = n + 3 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R T).liftOfKanComplex else
      if j.val = n + 4 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible S T).liftOfKanComplex else SSet.const x

/-- 三つの差の充填の共通面は一致する。 -/
lemma compositionCompatible (R S T : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    horn.IsCompatible (i := (Fin.last (n + 1)).castSucc.castSucc.castSucc)
      (fun j _ ↦ compositionFace R S T j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [compositionFace]
  split_ifs <;> try simp only [filler_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 合成ホーンの欠ける面の境界は、三つの差の球面となる。 -/
lemma composition_output_face
    (R S T : PtSimplex.RelStruct .const s (Fin.last (n + 1))) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc.castSucc ≫
      (compositionCompatible R S T).liftOfKanComplex =
      if j.val = n + 1 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S).map else
        if j.val = n + 2 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R T).map else
          if j.val = n + 3 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex S T).map else SSet.const x := by
  let q : Fin (n + 4) := (Fin.last n).castSucc.castSucc.castSucc
  have hq : (Fin.last (n + 1)).castSucc.castSucc.castSucc = q.succ := by
    apply Fin.ext; rfl
  by_cases hj : j ≤ q
  · rw (occs := .pos [1]) [hq]
    rw [stdSimplex.δ_comp_δ_assoc hj,
      (compositionCompatible R S T).δ_liftOfKanComplex _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_last] at hh
        have hjv := hj
        simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at hjv
        omega)]
    have hjv : j.val ≤ n := hj
    simp only [compositionFace]
    split_ifs <;> first
      | (exfalso; simp only [Fin.val_castSucc] at *; omega)
      | simp only [comp_const]
  · have hm : (Fin.last (n + 1)).castSucc.castSucc ≤ j := by
      simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at *
      omega
    rw [← stdSimplex.δ_comp_δ_assoc hm,
      (compositionCompatible R S T).δ_liftOfKanComplex _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hh
        have hjv := hm
        simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hjv
        omega)]
    simp only [compositionFace]
    split_ifs <;> try simp only [filler_face, Fin.val_last, Fin.val_castSucc,
      comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso; simp only [Fin.val_succ] at *; omega)

/-- 欠ける面は差の合成を実現する積の充填。 -/
def compositionMulStruct
    (R S T : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    PtSimplex.MulStruct (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex S T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R T) (Fin.last (n + 1)) where
  map := stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc.castSucc ≫
    (compositionCompatible R S T).liftOfKanComplex
  δ_castSucc_castSucc_map := by
    rw [composition_output_face]
    simp only [Fin.val_castSucc, Fin.val_last]
    rfl
  δ_succ_castSucc_map := by
    rw [composition_output_face]
    simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc]
    split_ifs <;> first | rfl | omega
  δ_succ_succ_map := by
    rw [composition_output_face]
    simp only [Fin.val_succ, Fin.val_last]
    split_ifs <;> first | rfl | omega
  δ_map_of_lt j hj := by
    rw [composition_output_face]
    have hjv : j.val < n + 1 := hj
    split_ifs <;> first | rfl | omega
  δ_map_of_gt j hj := by
    have hjb := j.isLt
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_last] at hj
    omega

/-- 三つの零ホモトピーの差は、ホモトピー群で合成する。 -/
theorem difference_comp
    (R S T : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    difference S T * difference R S = difference R T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (compositionMulStruct R S T)

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
