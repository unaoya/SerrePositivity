module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceComposition
public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceIdentity

/-!
概要：零である零ホモトピーの差を、定数の欠ける面を持つ充填へ取り替える。
方針：差の零ホモトピー・元の充填・退化単体を一つ高いホーンへ貼る。
規約：元の二つの零ホモトピーは単体として固定する。
使われ方：Goerss–Jardine VIII §1。零障害からの相対持ち上げの準備。
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
  (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
  (K : PtSimplex.RelStruct .const (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S) (Fin.last (n + 2)))

/-- 差の零ホモトピー、元の差の充填、退化単体を貼るホーン。 -/
def zeroFace (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n + 1 then K.map else
    if j.val = n + 2 then stdSimplex.σ (Fin.last (n + 2)) ≫ R.map else
      if j.val = n + 4 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex else SSet.const x

/-- 差の零ホモトピーの終面が、元の充填の差の面と一致する。 -/
lemma zeroCompatible :
    horn.IsCompatible (i := (Fin.last (n + 3)).castSucc) (fun j _ ↦ zeroFace R S K j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 3 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 3 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [zeroFace]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, diagonal_filler_face, filler_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.ext_iff, Fin.val_last, Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 欠ける面は、元の二つの零ホモトピーと定数面だけを持つ。 -/
lemma zero_output_face (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 3)).castSucc ≫
      (zeroCompatible R S K).liftOfKanComplex = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j := by
  by_cases hj : j ≤ (Fin.last (n + 2)).castSucc
  · have he : (Fin.last (n + 3)).castSucc = ((Fin.last (n + 2)).castSucc).succ := by
      apply Fin.ext; rfl
    rw (occs := .pos [1]) [he]
    rw [stdSimplex.δ_comp_δ_assoc hj,
      (zeroCompatible R S K).δ_liftOfKanComplex _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_last] at hh
        have hjv : j.val ≤ n + 2 := hj
        omega)]
    simp only [zeroFace, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, diagonal_filler_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         try simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ, Fin.le_def] at *
         first | contradiction | omega)
  · have hjlast : j = Fin.last (n + 3) := by
      apply Fin.ext
      have hjb := j.isLt
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last] at hj ⊢
      omega
    subst j
    rw [← stdSimplex.δ_comp_δ_assoc (show Fin.last (n + 3) ≤ Fin.last (n + 3) from le_rfl),
      (zeroCompatible R S K).δ_liftOfKanComplex _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ] at hh
        omega)]
    simp only [zeroFace, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, Fin.val_succ, Fin.val_last]
    split_ifs <;> try simp only [filler_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, Fin.val_last]
    all_goals (try split_ifs) <;> first | rfl | omega

/-- 零である差には、定数の差の面を持つ充填がある。 -/
theorem exists_zero_filler (he : difference R S = 1) :
    ∃ φ : (Δ[n + 3] : SSet.{u}) ⟶ X, ∀ j, stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j := by
  obtain ⟨K⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (n + 2))).1
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff .const (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S)).1 he.symm)
  exact ⟨stdSimplex.δ (Fin.last (n + 3)).castSucc ≫ (zeroCompatible R S K).liftOfKanComplex,
    zero_output_face R S K⟩

/-- 定数の差の面を持つ充填は零の差を表す。 -/
theorem difference_eq_one_of_zero_filler (φ : (Δ[n + 3] : SSet.{u}) ⟶ X)
    (hφ : ∀ j, stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j) : difference R S = 1 := by
  let hh j (_ : j ≠ (Fin.last (n + 1)).castSucc.castSucc) := hφ j
  rw [difference_eq_ofFiller R S φ hh]
  have he : ofFiller R S φ hh = .const := by
    apply RelativeMorphism.ext
    change stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ φ = SSet.const x
    rw [hφ]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  rw [he]
  rfl

/-- 差の零性は、固定した二つの零ホモトピーと定数面の充填の存在と同値。 -/
theorem difference_eq_one_iff_zero_filler :
    difference R S = 1 ↔
      ∃ φ : (Δ[n + 3] : SSet.{u}) ⟶ X, ∀ j, stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j :=
  ⟨exists_zero_filler R S, fun ⟨φ, hφ⟩ ↦ difference_eq_one_of_zero_filler R S φ hφ⟩

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
