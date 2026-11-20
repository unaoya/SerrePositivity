module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationMultiplication

/-!
概要：高次ホモトピー類の積の面添字独立性と左因子の充填。
方針：隣接面の比較と可換性を用い、指定した二面のホーンを充填する。
規約：MulStruct の三面の順序は第二因子、積、第一因子。
使われ方：Kerodon §3.2.3（Tag 00W3）、Goerss–Jardine I §7。球面的境界の交代関係。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：高次の積の充填は任意の面添字で商上の積を計算する。
方針：最後の添字から逆向きに帰納し、隣接面で因子を交換して可換性を使う。
規約：単体の実際の次数は n + 2。
使われ方：Kerodon Lemma 3.2.3.9（Tag 00WC）、Theorem 3.2.2.10（Tag 00VU）。境界の面の消去。 -/
theorem KanHomotopyGroup.mul_eq_at {X : SSet.{u}} [KanComplex X]
    {n : ℕ} {x : X _⦋0⦌} {f g a : X.PtSimplex (n + 2) x} {i : Fin (n + 2)}
    (h : PtSimplex.MulStruct f g a i) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a := by
  induction i using Fin.reverseInduction generalizing f g a with
  | last => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq h
  | cast i ih =>
    obtain ⟨b, ⟨hb⟩⟩ := PtSimplex.MulStruct.nonempty g f i.succ
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_unique_at h (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip hb)
    rw [he, ← ih hb, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_comm]

/-- 概要：第二因子と積を指定した積の充填は存在する。
方針：第一因子の面を欠くホーンを Kan 性で埋め、その面を取る。
規約：面添字と次数は任意の正次数。
使われ方：Kerodon §3.2.3（Tag 00W3）、Goerss–Jardine I §7。球面的境界の逐次消去。 -/
theorem exists_left_factor {X : SSet.{u}} [KanComplex X]
    {n : ℕ} {x : X _⦋0⦌} (g a : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    ∃ f : X.PtSimplex (n + 1) x, Nonempty (PtSimplex.MulStruct f g a i) := by
  let α (j : Fin (n + 3)) (_ : j ≠ i.succ.succ) : (Δ[n + 1] : SSet.{u}) ⟶ X :=
    if j = i.castSucc.castSucc then g.map else
      if j = i.castSucc.succ then a.map else SSet.const x
  have δ_α (j) (hj) (k : Fin (n + 2)) :
      stdSimplex.δ k ≫ α j hj = SSet.const x := by
    dsimp [α]; split_ifs <;> simp
  have hα : horn.IsCompatible α := fun _ _ _ _ _ ↦ by simp [δ_α]
  refine ⟨.mk (stdSimplex.δ i.succ.succ ≫ hα.liftOfKanComplex) ?_,
    ⟨{map := hα.liftOfKanComplex
      δ_succ_castSucc_map := ?_
      δ_castSucc_castSucc_map := ?_
      δ_map_of_lt _ _ := ?_
      δ_map_of_gt _ _ := ?_ }⟩⟩
  · ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    by_cases! hj : j ≤ i.succ
    · rw [stdSimplex.δ_comp_δ_assoc (by grind),
        hα.δ_liftOfKanComplex .., δ_α _ (by grind)]
    · obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
      rw [← dsimp% stdSimplex.δ_comp_δ_assoc (i := i.succ.succ) (j := j) (by grind),
        hα.δ_liftOfKanComplex .., δ_α _ (by grind)]
  all_goals grind [horn.IsCompatible.δ_liftOfKanComplex]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
