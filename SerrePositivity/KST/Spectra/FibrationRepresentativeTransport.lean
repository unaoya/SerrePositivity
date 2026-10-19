module

public import SerrePositivity.KST.Spectra.FibrationExactness

/-!
概要：Kan fibration の下でホモトピー類が一致する代表を厳密に一致する代表へ移す。
方針：元の代表を最後から二番目の面に置き、底の RelStruct に沿うホーンを持ち上げる。
規約：元の upstairs の類を保持し、射影は指定した downstairs の単体そのもの。
使われ方：Goerss–Jardine VIII §1。塔の整合する代表と収束の構成。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.FibrationRepresentatives

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 底の相対ホモトピーを持ち上げ、指定した射影を持つ同じ類の単体を得る。 -/
theorem exists_transport {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) {n : ℕ} (a : E.PtSimplex (n + 1) e)
    (s : B.PtSimplex (n + 1) (p.app _ e))
    (r : PtSimplex.RelStruct (mapSimplex p rfl a) s (Fin.last (n + 1))) :
    ∃ b : E.PtSimplex (n + 1) e, mapSimplex p rfl b = s ∧
      Nonempty (PtSimplex.RelStruct a b (Fin.last (n + 1))) := by
  let α (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
    if j.val = n + 1 then a.map else SSet.const e
  have hαface (j) (hj) (k : Fin (n + 2)) : stdSimplex.δ k ≫ α j hj = SSet.const e := by
    dsimp [α]
    split_ifs <;> simp
  have hα : horn.IsCompatible α := fun _ _ _ _ _ ↦ by simp [hαface]
  have hcomm (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
      α j hj ≫ p = stdSimplex.δ j ≫ r.map := by
    by_cases hj₀ : j.val = n + 1
    · have he : j = (Fin.last (n + 1)).castSucc := Fin.ext hj₀
      dsimp [α]
      rw [ite_eq_left hj₀, he]
      exact r.δ_castSucc_map.symm
    · have hj' : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
      have hlt : j < (Fin.last (n + 1)).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        omega
      dsimp [α]
      rw [ite_eq_right hj₀, const_comp, r.δ_map_of_lt j hlt]
  obtain ⟨φ, hφ, hp⟩ := hα.exists_lift p r.map hcomm
  let b : E.PtSimplex (n + 1) e :=
    { map := stdSimplex.δ (Fin.last (n + 2)) ≫ φ
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
          hφ _ (Fin.castSucc_ne_last j)]
        exact hαface _ (Fin.castSucc_ne_last j) _ }
  refine ⟨b, ?_, ⟨{
    map := φ
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }⟩⟩
  · apply RelativeMorphism.ext
    change (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ≫ p = s.map
    rw [Category.assoc, hp]
    simpa only [Fin.succ_last] using r.δ_succ_map
  · simpa [α] using hφ (Fin.last (n + 1)).castSucc (Fin.castSucc_ne_last _)
  · rw [Fin.succ_last]
  · intro j hj
    rw [hφ j (Fin.ne_last_of_lt (hj.trans (Fin.castSucc_lt_last _)))]
    dsimp [α]
    apply ite_eq_right
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
    omega
  · intro j hj
    exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 指定した downstairs の代表を厳密に射影する、指定した upstairs の類の代表がある。 -/
theorem exists_representative {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) {n : ℕ}
    (a : KanHomotopyGroup E n e) (s : B.PtSimplex (n + 1) (p.app _ e))
    (h : KanHomotopyGroup.map p rfl a = KanHomotopyGroup.mk s) :
    ∃ b : E.PtSimplex (n + 1) e, KanHomotopyGroup.mk b = a ∧ mapSimplex p rfl b = s := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep a
  change KanHomotopyGroup.map p rfl (KanHomotopyGroup.mk t) = KanHomotopyGroup.mk s at h
  rw [KanHomotopyGroup.map_mk] at h
  obtain ⟨r⟩ := (simplexRel_iff_relStruct (Fin.last (n + 1))).1
    ((KanHomotopyGroup.mk_eq_iff _ _).1 h)
  obtain ⟨b, hb, ⟨hr⟩⟩ := exists_transport p e t s r
  exact ⟨b, (KanHomotopyGroup.sound hr).symm, hb⟩

/-- 基点の像の標準同定を指定した形での、厳密な射影を持つ代表。 -/
theorem exists_representative_at {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) {b : B _⦋0⦌}
    (hpoint : p.app _ e = b) {n : ℕ} (a : KanHomotopyGroup E n e)
    (s : B.PtSimplex (n + 1) b) (h : KanHomotopyGroup.map p hpoint a = KanHomotopyGroup.mk s) :
    ∃ t : E.PtSimplex (n + 1) e, KanHomotopyGroup.mk t = a ∧ mapSimplex p hpoint t = s := by
  subst b
  exact exists_representative p e a s h

end
end SerrePositivity.KST.Spectra.FibrationRepresentatives
