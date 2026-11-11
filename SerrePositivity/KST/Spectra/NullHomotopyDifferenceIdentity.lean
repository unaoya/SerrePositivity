module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceClass

/-!
概要：同じ零ホモトピーを比較したときの差は単位元。
方針：零ホモトピーの最後の退化を差のホーンの充填として使う。
規約：差の類の向きと基点を具体的な退化単体で固定する。
使われ方：Goerss–Jardine VIII §1。lim¹ の基点との比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyDifference

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
  {s : X.PtSimplex (n + 1) x}

/-- 最後の退化は同じ零ホモトピーを二面に持つ差のホーンを充填する。 -/
lemma diagonal_filler_face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.σ (Fin.last (n + 2)) ≫ R.map = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R R j := by
  by_cases h₀ : j.val = n + 2
  · have he : j = (Fin.last (n + 2)).castSucc := Fin.ext h₀
    subst j
    rw [stdSimplex.δ_comp_σ_self_assoc]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  by_cases h₁ : j.val = n + 3
  · have he : j = (Fin.last (n + 2)).succ := Fin.ext h₁
    subst j
    rw [stdSimplex.δ_comp_σ_succ_assoc]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  have hjlast : j ≠ Fin.last (n + 3) := fun he ↦ h₁ (congrArg Fin.val he)
  obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last hjlast
  simp only [Fin.val_castSucc] at h₀ h₁
  have hj : j ≤ (Fin.last (n + 1)).castSucc := by
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]
    have hjb := j.isLt
    omega
  rw [show Fin.last (n + 2) = (Fin.last (n + 1)).succ from (Fin.succ_last _).symm,
    stdSimplex.δ_comp_σ_of_le_assoc hj, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face,
    ite_eq_right (show j ≠ Fin.last (n + 2) from fun he ↦ h₀ (congrArg Fin.val he)), comp_const]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, Fin.val_castSucc, ite_eq_right h₀, ite_eq_right h₁]

/-- 同じ零ホモトピーの差を充填する最後の退化の欠ける面は定数。 -/
lemma diagonal_missing_face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫
      stdSimplex.σ (Fin.last (n + 2)) ≫ R.map = SSet.const x := by
  rw [show Fin.last (n + 2) = (Fin.last (n + 1)).succ from (Fin.succ_last _).symm,
    stdSimplex.δ_comp_σ_of_le_assoc (show (Fin.last (n + 1)).castSucc ≤
      (Fin.last (n + 1)).castSucc from le_rfl), _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face]
  rw [ite_eq_right (Fin.castSucc_ne_last _), comp_const]

/-- 差の構成は、同じ零ホモトピー同士では単位元になる。 -/
theorem difference_self [KanComplex X] (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    difference R R = 1 := by
  have hφ (j : Fin (n + 4)) (_ : j ≠ (Fin.last (n + 1)).castSucc.castSucc) :=
    diagonal_filler_face R j
  rw [difference_eq_ofFiller R R (stdSimplex.σ (Fin.last (n + 2)) ≫ R.map) hφ]
  have hs : ofFiller R R (stdSimplex.σ (Fin.last (n + 2)) ≫ R.map) hφ = .const := by
    apply RelativeMorphism.ext
    exact diagonal_missing_face R
  rw [hs]
  rfl

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
