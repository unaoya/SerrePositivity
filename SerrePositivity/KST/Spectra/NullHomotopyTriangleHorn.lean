module

public import SerrePositivity.KST.Spectra.NullTransportDifference

/-!
概要：二つの零ホモトピーを三角形の二辺に置く相対ホーン。
方針：最後の面を欠ける面とし、その面を二つの球面の相対ホモトピーとして読む。
規約：充填は任意。Kan 性や fibration はこのホーンの組立てには不要。
使われ方：Goerss–Jardine VIII §1。核の障害の単射性に使う相対持ち上げ。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.NullHomotopyTriangle
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
  {s t : X.PtSimplex (n + 1) x}
  (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
  (S : PtSimplex.RelStruct .const t (Fin.last (n + 1)))

/-- 三角形の二つの零ホモトピーの面。 -/
def face (j : Fin (n + 4)) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
  if j.val = n + 1 then R.map else if j.val = n + 2 then S.map else SSet.const x

/-- 二つの零ホモトピーの始面はともに定数なのでホーンは互換。 -/
lemma compatible : horn.IsCompatible (i := Fin.last (n + 3)) (fun j _ ↦ face R S j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 3 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 3 := fun he ↦ hk (Fin.ext he)
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

variable (φ : (Δ[n + 3] : SSet.{u}) ⟶ X)
  (hφ : ∀ j, j ≠ Fin.last (n + 3) → stdSimplex.δ j ≫ φ = face R S j)

include hφ in
/-- 欠ける最後の面は二つの球面を相対に結ぶ。 -/
lemma output_face (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 3)) ≫ φ =
      if j.val = n + 1 then s.map else if j.val = n + 2 then t.map else SSet.const x := by
  rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
    hφ _ (Fin.castSucc_ne_last j)]
  simp only [face, Fin.val_castSucc]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.ext_iff, Fin.val_last, Fin.val_pred] at *
       omega)

/-- 任意の三角形の充填から相対ホモトピーを取り出す。 -/
def relation : PtSimplex.RelStruct s t (Fin.last (n + 1)) where
  map := stdSimplex.δ (Fin.last (n + 3)) ≫ φ
  δ_castSucc_map := by rw [output_face R S φ hφ]; simp
  δ_succ_map := by rw [output_face R S φ hφ]; simp
  δ_map_of_lt j hj := by
    rw [output_face R S φ hφ]
    have hjv : j.val < n + 1 := hj
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 充填を三面とも書くと、通常の移送の三角形となる。 -/
lemma filler_face (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ φ = NullHomotopyTransport.triangleFace R (relation R S φ hφ) S j := by
  by_cases hj : j = Fin.last (n + 3)
  · subst j
    simp only [NullHomotopyTransport.triangleFace, Fin.val_last,
      ite_eq_right (by omega : n + 3 ≠ n + 1), ite_eq_right (by omega : n + 3 ≠ n + 2),
      ite_true]
    rfl
  · rw [hφ j hj]
    have hjv : j.val ≠ n + 3 := fun he ↦ hj (Fin.ext he)
    simp only [face, NullHomotopyTransport.triangleFace, ite_eq_right hjv]

end
end SerrePositivity.KST.Spectra.NullHomotopyTriangle
