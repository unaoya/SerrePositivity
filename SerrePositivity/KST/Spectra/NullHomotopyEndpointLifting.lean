module

public import SerrePositivity.KST.Spectra.NullHomotopyStrictLifting

/-!
概要：Kan fibration の下で、零ホモトピーを球面の終点ごと持ち上げる。
方針：最後の面を除いた全ての面を upstairs の定数として相対ホーンを充填する。
規約：upstairs の球面を固定せず、持ち上げた最後の面から構成する。
使われ方：Goerss–Jardine VIII §1。任意の lim¹ の代表を塔の核で実現する一工程。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.NullHomotopyEndpointLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 指定した downstairs の零ホモトピーを、終点の球面と共に厳密に持ち上げる。 -/
theorem exists_lift {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {e : E _⦋0⦌} {b : B _⦋0⦌} (hb : p.app _ e = b) {n : ℕ}
    {t : B.PtSimplex (n + 1) b}
    (T : PtSimplex.RelStruct .const t (Fin.last (n + 1))) :
    ∃ s : E.PtSimplex (n + 1) e,
      ∃ R : PtSimplex.RelStruct .const s (Fin.last (n + 1)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p hb s = t ∧ R.map ≫ p = T.map := by
  have hc : horn.IsCompatible (i := Fin.last (n + 2))
      (fun _ _ ↦ (SSet.const e : (Δ[n + 1] : SSet.{u}) ⟶ E)) := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    simp only [comp_const]
  have hd (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
      (SSet.const e : (Δ[n + 1] : SSet.{u}) ⟶ E) ≫ p = stdSimplex.δ j ≫ T.map := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.null_face, ite_eq_right hj, const_comp, hb]
  obtain ⟨φ, hφ, hp⟩ := hc.exists_lift p T.map hd
  let s : E.PtSimplex (n + 1) e := {
    map := stdSimplex.δ (Fin.last (n + 2)) ≫ φ
    comm := by
      ext j : 1
      simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
      rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
        hφ _ (Fin.castSucc_ne_last j), comp_const] }
  let R : PtSimplex.RelStruct .const s (Fin.last (n + 1)) := {
    map := φ
    δ_castSucc_map := hφ _ (Fin.castSucc_ne_last _)
    δ_succ_map := by simp only [Fin.succ_last]; rfl
    δ_map_of_lt j hj := hφ j (by
      intro he
      have hval := congrArg Fin.val he
      have hjv : j.val < n + 1 := hj
      simp only [Fin.val_last] at hval
      omega)
    δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim }
  refine ⟨s, R, ?_, hp⟩
  apply RelativeMorphism.ext
  change (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ≫ p = t.map
  rw [Category.assoc, hp]
  simpa only [Fin.succ_last] using T.δ_succ_map

end
end SerrePositivity.KST.Spectra.NullHomotopyEndpointLifting
