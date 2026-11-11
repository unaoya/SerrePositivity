module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyProductIndex

/-!
概要：同じ境界を持つ二つの零ホモトピーの差の球面代表。
方針：二つの充填を隣り合う最後の二面へ貼り、欠ける面を Kan 充填から取り出す。
規約：差は一つ高いホモトピー群の境界定数単体として構成する。
使われ方：Goerss–Jardine VIII §1。塔の零ホモトピーのずれと lim¹ の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyDifference
end SerrePositivity.KST.Spectra.NullHomotopyDifference
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference
open _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} {s : X.PtSimplex (n + 1) x}

/-- 最後の面だけが指定単体となる零ホモトピーの全ての面の公式。 -/
lemma null_face (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ R.map = if j = Fin.last (n + 2) then s.map else SSet.const x := by
  by_cases hj : j = Fin.last (n + 2)
  · subst j
    rw [ite_eq_left rfl]
    simpa only [Fin.succ_last] using R.δ_succ_map
  · rw [ite_eq_right hj]
    by_cases hj' : j = (Fin.last (n + 1)).castSucc
    · subst j
      exact R.δ_castSucc_map
    · apply R.δ_map_of_lt
      have hjb := j.isLt
      simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.lt_def] at hj hj' ⊢
      omega

/-- 差のホーンの二つの非定数面。欠ける面は n+1。 -/
def face (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (j : Fin (n + 4)) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
  if j.val = n + 2 then R.map else if j.val = n + 3 then S.map else SSet.const x

/-- 同じ最後の面を持つ二つの零ホモトピーからのホーンは互換。 -/
lemma compatible (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    horn.IsCompatible (i := (Fin.last (n + 1)).castSucc.castSucc) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.val_pred, Fin.coe_castPred] at *
       omega)

/-- 差のホーンの欠ける面の境界は全て定数。 -/
lemma output_face (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ X)
    (hφ : ∀ j, j ≠ (Fin.last (n + 1)).castSucc.castSucc →
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j) (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ φ = SSet.const x := by
  let q : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  have hq : (Fin.last (n + 1)).castSucc.castSucc = q.succ := by apply Fin.ext; rfl
  by_cases hj : j ≤ q
  · rw [hq, stdSimplex.δ_comp_δ_assoc hj, hφ _ (by
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      have hjv := hj
      simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at hjv
      omega)]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_last, q, Fin.le_def] at *
         omega)
  · have hm : (Fin.last (n + 1)).castSucc ≤ j := by
      simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at *
      omega
    rw [← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hh
      have hjv := hm
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hjv
      omega)]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_last, q, Fin.le_def] at *
         omega)

/-- 二つの零ホモトピーの差を表す境界定数単体。 -/
def simplex [KanComplex X] (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    X.PtSimplex (n + 2) x where
  map := stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.output_face R S _ (fun k hk ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).δ_liftOfKanComplex k hk) j

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.compatible := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.null_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.output_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.output_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.simplex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NullHomotopyDifference.simplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex._proof_1
