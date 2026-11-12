module

public import SerrePositivity.KST.Spectra.FibrationAdjacentComparison

/-!
概要：比較ホーンの出力の終点と、境界定数の持ち上げの終点のホモトピー類を比較する。
方針：もう一つの持ち上げが終点で定数なら、比較単体は隣接二面の RelStruct になる。
規約：ホモトピー類の等式を証明し、単体の等式や任意の充填の選択を仮定しない。
使われ方：Goerss–Jardine I §8。fiber 内の path の終点を元の連結射へ戻す。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.AdjacentLiftComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B Y : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}
  (U : E.PtSimplex (n + 1) e) (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
  {y : Y _⦋0⦌} (h : E ⟶ Y) (hpoint : h.app _ e = y)
  (hV : V.map ≫ h = SSet.const y)
  (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
  (hface : ∀ j, j ≠ Fin.last (n + 2) → stdSimplex.δ j ≫ φ = face U V j)

/-- 概要：最後の面の終点は境界定数単体になる。
方針：各境界を既知の面へ移し、U の境界定数性と V の終点定数性を使う。
規約：基点の移送だけを明示する。
使われ方：Goerss–Jardine I §8。fiber 内の path の終点の群の代表。 -/
def endpointSimplex (U : E.PtSimplex (n + 1) e) (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (h : E ⟶ Y) (hpoint : h.app _ e = y) (hV : V.map ≫ h = SSet.const y)
    (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hface : ∀ j, j ≠ Fin.last (n + 2) → stdSimplex.δ j ≫ φ = face U V j) :
    Y.PtSimplex (n + 1) y where
  map := stdSimplex.δ (Fin.last (n + 2)) ≫ φ ≫ h
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
      ← Category.assoc (stdSimplex.δ j.castSucc) φ h,
      hface _ (Fin.castSucc_ne_last j)]
    simp only [face, Fin.val_castSucc]
    split_ifs
    · rw [hV, comp_const]
    · rw [← Category.assoc, PtSimplex.δ_map, const_comp, hpoint]
    · rw [const_comp, hpoint, comp_const]

/-- 概要：終点を評価した比較単体は、元の持ち上げと出力を結ぶ RelStruct。
方針：最後の隣接二面を明示し、それより前の面を定数として計算する。
規約：元の U の終点から出力の終点への向き。
使われ方：Goerss–Jardine I §8。終点のホモトピー類の一致。 -/
def endpointRel : PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex h hpoint U)
    (endpointSimplex U V h hpoint hV φ hface) (Fin.last (n + 1)) where
  map := φ ≫ h
  δ_castSucc_map := by
    rw [← Category.assoc, hface _ (Fin.castSucc_ne_last _)]
    simp only [face, Fin.val_last, Fin.val_castSucc]
    rw [ite_eq_right (by omega), ite_true]
    rfl
  δ_succ_map := rfl
  δ_map_of_lt j hj := by
    have hj' : j.val < n + 1 := hj
    have hn : j ≠ Fin.last (n + 2) := by
      intro he; have := congrArg Fin.val he; simp only [Fin.val_last] at this; omega
    rw [← Category.assoc, hface j hn]
    simp only [face]
    split_ifs
    · exact hV
    · omega
    · rw [const_comp, hpoint]
  δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 概要：出力の終点のホモトピー類は元の U の終点の類に等しい。
方針：構成した隣接二面の RelStruct を商へ送る。
規約：任意の Kan な終点空間 Y。
使われ方：Goerss–Jardine I §8。逆符号で現れる連結射の値を同定する。 -/
lemma endpoint_class [KanComplex E] [KanComplex Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex U V h hpoint hV φ hface) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map h hpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk U) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (endpointRel U V h hpoint hV φ hface)).symm

end
end SerrePositivity.KST.Spectra.AdjacentLiftComparison
