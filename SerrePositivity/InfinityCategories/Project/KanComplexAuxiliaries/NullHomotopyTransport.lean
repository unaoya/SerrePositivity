module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference

/-!
概要：球面の相対ホモトピーに沿って零ホモトピーを移す Kan 充填。
方針：零ホモトピーと相対ホモトピーを最後の三面の両端へ置き、中央を充填する。
規約：相対ホモトピーの最後の二面の順序は移送元、移送先。
使われ方：Goerss–Jardine VIII §1。lim¹ 障害の球面代表変更。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyTransport
end SerrePositivity.KST.Spectra.NullHomotopyTransport
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport
open _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
  {s t : X.PtSimplex (n + 1) x}

/-- 最後の二面に置かれた相対ホモトピーの全ての面。 -/
lemma relation_face (A : PtSimplex.RelStruct s t (Fin.last (n + 1))) (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ A.map =
      if j.val = n + 1 then s.map else if j.val = n + 2 then t.map else SSet.const x := by
  by_cases h₀ : j.val = n + 1
  · have he : j = (Fin.last (n + 1)).castSucc := Fin.ext h₀
    subst j
    rw [ite_eq_left h₀]
    exact A.δ_castSucc_map
  by_cases h₁ : j.val = n + 2
  · have he : j = (Fin.last (n + 1)).succ := Fin.ext h₁
    subst j
    rw [ite_eq_right h₀, ite_eq_left h₁]
    exact A.δ_succ_map
  rw [ite_eq_right h₀, ite_eq_right h₁]
  apply A.δ_map_of_lt
  have hj := j.isLt
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
  omega

/-- 移送ホーンの既知の二面。中央の n+2 面を欠く。 -/
def face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct s t (Fin.last (n + 1))) (j : Fin (n + 4)) :
    (Δ[n + 2] : SSet.{u}) ⟶ X :=
  if j.val = n + 1 then R.map else if j.val = n + 3 then A.map else SSet.const x

/-- 零ホモトピーの終面と相対ホモトピーの始面が一致する移送ホーン。 -/
lemma compatible (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct s t (Fin.last (n + 1))) :
    horn.IsCompatible (i := (Fin.last (n + 2)).castSucc) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face R A j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 2 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.relation_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 移送ホーンの中央の面の境界は移送先の零ホモトピーの境界。 -/
lemma output_face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct s t (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ X)
    (hφ : ∀ j, j ≠ (Fin.last (n + 2)).castSucc → stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face R A j)
    (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 2)).castSucc ≫ φ =
      if j.val = n + 2 then t.map else SSet.const x := by
  by_cases hj : j ≤ (Fin.last (n + 1)).castSucc
  · have he : (Fin.last (n + 2)).castSucc = ((Fin.last (n + 1)).castSucc).succ := by
      apply Fin.ext; rfl
    rw [he, stdSimplex.δ_comp_δ_assoc hj, hφ _ (by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      have hjv : j.val ≤ n + 1 := hj
      omega)]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.le_def] at *
         omega)
  · have hjlast : j = Fin.last (n + 2) := by
      apply Fin.ext
      have hjb := j.isLt
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last] at hj ⊢
      omega
    subst j
    rw [← stdSimplex.δ_comp_δ_assoc (show Fin.last (n + 2) ≤ Fin.last (n + 2)
      from le_rfl), hφ _ (by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ] at hh
        omega)]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face, Fin.val_succ, Fin.val_last]
    rw [ite_eq_right (by omega)]
    simp only [ite_true]
    simpa only [Fin.succ_last] using A.δ_succ_map

/-- 移送された零ホモトピー。 -/
def transport [KanComplex X] (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct s t (Fin.last (n + 1))) :
    PtSimplex.RelStruct .const t (Fin.last (n + 1)) where
  map := stdSimplex.δ (Fin.last (n + 2)).castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).liftOfKanComplex
  δ_castSucc_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.output_face R A _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).δ_liftOfKanComplex j hj)]
    simp
  δ_succ_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.output_face R A _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).δ_liftOfKanComplex j hj)]
    simp
  δ_map_of_lt j hj := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.output_face R A _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).δ_liftOfKanComplex j hj)]
    rw [ite_eq_right (by
      have hjv : j.val < n + 1 := hj
      omega)]
  δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 移送の充填の三つの非定数面を含む全ての面の式。 -/
lemma filler_face [KanComplex X] (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct s t (Fin.last (n + 1))) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).liftOfKanComplex =
      if j.val = n + 1 then R.map else if j.val = n + 2 then (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport R A).map else
        if j.val = n + 3 then A.map else SSet.const x := by
  by_cases hj : j.val = n + 2
  · have he : j = (Fin.last (n + 2)).castSucc := Fin.ext hj
    subst j
    rw [ite_eq_right (by omega), ite_eq_left hj]
    rfl
  · rw [(_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).δ_liftOfKanComplex j (fun he ↦ hj (congrArg Fin.val he))]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face]
    split_ifs <;> rfl

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.compatible := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.filler_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.filler_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.output_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.output_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.relation_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.relation_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.transport := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.transport._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.transport._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.transport._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.transport._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyTransport.transport.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport.congr_simp
