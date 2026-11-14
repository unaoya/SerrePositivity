module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.NullHomotopyTransport
public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceComposition

/-!
概要：共通の相対ホモトピーに沿う移送は零ホモトピーの差を保つ。
方針：移送の二つの充填と移送先の差の充填を一つ高いホーンに貼る。
規約：移送の充填は任意。選択した充填の自然性は仮定しない。
使われ方：Goerss–Jardine VIII §1。lim¹ 障害の球面代表変更への不変性。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} {n : ℕ}
  {s t : X.PtSimplex (n + 1) x}
  (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
  (A : PtSimplex.RelStruct s t (Fin.last (n + 1)))
  (U V : PtSimplex.RelStruct .const t (Fin.last (n + 1)))

/-- 移送の三つの非定数面。 -/
def triangleFace (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct s t (Fin.last (n + 1)))
    (U : PtSimplex.RelStruct .const t (Fin.last (n + 1))) (j : Fin (n + 4)) :
    (Δ[n + 2] : SSet.{u}) ⟶ X :=
  if j.val = n + 1 then R.map else if j.val = n + 2 then U.map else
    if j.val = n + 3 then A.map else SSet.const x

variable (φ ψ : (Δ[n + 3] : SSet.{u}) ⟶ X)
  (hφ : ∀ j, stdSimplex.δ j ≫ φ = triangleFace R A U j)
  (hψ : ∀ j, stdSimplex.δ j ≫ ψ = triangleFace S A V j)

/-- 移送の二つの充填と移送先の差の充填を貼る。 -/
def comparisonFace (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n + 2 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible U V).liftOfKanComplex else
    if j.val = n + 3 then φ else if j.val = n + 4 then ψ else SSet.const x

include hφ hψ in
/-- 移送の共通面は、選択によらず比較ホーンを与える。 -/
lemma comparisonCompatible :
    horn.IsCompatible (i := (Fin.last (n + 1)).castSucc.castSucc.castSucc)
      (fun j _ ↦ comparisonFace U V φ ψ j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [comparisonFace]
  split_ifs <;> try simp only [hφ, hψ, triangleFace, NullHomotopyDifference.filler_face,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 比較ホーンの欠ける面の三面は、移送先の差と移送元の二つの零ホモトピー。 -/
lemma comparison_output_face (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc.castSucc ≫
      (comparisonCompatible R S A U V φ ψ hφ hψ).liftOfKanComplex =
      if j.val = n + 1 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex U V).map else
        if j.val = n + 2 then R.map else if j.val = n + 3 then S.map else SSet.const x := by
  let q : Fin (n + 4) := (Fin.last n).castSucc.castSucc.castSucc
  have hq : (Fin.last (n + 1)).castSucc.castSucc.castSucc = q.succ := by
    apply Fin.ext; rfl
  by_cases hj : j ≤ q
  · rw (occs := .pos [1]) [hq]
    rw [stdSimplex.δ_comp_δ_assoc hj,
      (comparisonCompatible R S A U V φ ψ hφ hψ).δ_liftOfKanComplex _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_last] at hh
        have hjv := hj
        simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at hjv
        omega)]
    have hjv : j.val ≤ n := hj
    simp only [comparisonFace]
    split_ifs <;> first
      | (exfalso; simp only [Fin.val_castSucc] at *; omega)
      | simp only [comp_const]
  · have hm : (Fin.last (n + 1)).castSucc.castSucc ≤ j := by
      simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at *
      omega
    rw [← stdSimplex.δ_comp_δ_assoc hm,
      (comparisonCompatible R S A U V φ ψ hφ hψ).δ_liftOfKanComplex _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hh
        have hjv := hm
        simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hjv
        omega)]
    simp only [comparisonFace]
    split_ifs <;> try simp only [hφ, hψ, triangleFace, NullHomotopyDifference.filler_face,
      Fin.val_last, Fin.val_castSucc, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso; simp only [Fin.val_succ] at *; omega)

include hφ hψ in
/-- 任意の二つの移送充填は差の類を保存する。 -/
theorem difference_eq_of_transport_fillers :
    NullHomotopyDifference.difference R S = NullHomotopyDifference.difference U V := by
  let θ := stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc.castSucc ≫
    (comparisonCompatible R S A U V φ ψ hφ hψ).liftOfKanComplex
  have hθ (j : Fin (n + 4)) (hj : j ≠ (Fin.last (n + 1)).castSucc.castSucc) :
      stdSimplex.δ j ≫ θ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j := by
    rw [show θ = _ from rfl, comparison_output_face R S A U V φ ψ hφ hψ j]
    have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
    simp only [ite_eq_right hj', _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  rw [NullHomotopyDifference.difference_eq_ofFiller R S θ hθ]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  exact (comparison_output_face R S A U V φ ψ hφ hψ
    (Fin.last (n + 1)).castSucc.castSucc).trans (by simp)

end
end SerrePositivity.KST.Spectra.NullHomotopyTransport
