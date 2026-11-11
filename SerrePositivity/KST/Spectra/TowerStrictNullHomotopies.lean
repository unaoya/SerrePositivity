module

public import SerrePositivity.KST.Spectra.NullHomotopyStrictLifting
public import SerrePositivity.KST.Spectra.TowerNullHomotopyNormalization

/-!
概要：零障害を持つ球面の塔に厳密に整合する零ホモトピーを構成する。
方針：差が零となる族へ選択を直し、Kan fibration による相対持ち上げを順次使う。
規約：各段で指定した元の零ホモトピーとの差が零であることを帰納不変量にする。
使われ方：Goerss–Jardine VIII §1。Milnor 比較の核の零障害判定。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NullHomotopyDifference

namespace NullHomotopyStrictLifting

/-- 指定した基点と球面の同定を含めた厳密な零ホモトピーの調整。 -/
theorem exists_adjust_to {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] {e : E _⦋0⦌} {b : B _⦋0⦌} (hb : p.app _ e = b)
    {n : ℕ} {s : E.PtSimplex (n + 1) e} {t : B.PtSimplex (n + 1) b}
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p hb s = t)
    (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (T : PtSimplex.RelStruct .const t (Fin.last (n + 1)))
    (he : difference T (mapNullTo p hb hs R) = 1) :
    ∃ U : PtSimplex.RelStruct .const s (Fin.last (n + 1)),
      U.map ≫ p = T.map ∧ difference U R = 1 := by
  subst t
  subst b
  exact exists_adjust p R T he

end NullHomotopyStrictLifting

namespace PointedFibrationTower

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)
  (s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
  (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (s (n + 1)) = s n)
  (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))
  (hr : ∀ n, nullHomotopyDifferenceFamily X p r s hs R n = 1)

include hr in
/-- 前段を厳密に射影する次段を、元の零ホモトピーとの差を零に保って作る。 -/
lemma exists_next_nullHomotopy (n : ℕ)
    (U : {U : PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)) // difference U (R n) = 1}) :
    ∃ V : PtSimplex.RelStruct .const (s (n + 1)) (Fin.last (r + 1)),
      V.map ≫ (p n).right = U.val.map ∧ difference V (R (n + 1)) = 1 := by
  apply NullHomotopyStrictLifting.exists_adjust_to (p n).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (R (n + 1)) U.val
  rw [← difference_comp U.val (R n)
    (mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (R (n + 1))),
    U.property]
  exact mul_one _ |>.trans (hr n)

/-- 各段で元の零ホモトピーとの差が零となる、整合する族を帰納的に選ぶ。 -/
def strictNullHomotopy : ∀ n,
    {U : PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)) // difference U (R n) = 1}
  | 0 => ⟨R 0, difference_self _⟩
  | n + 1 =>
    let hex := exists_next_nullHomotopy X p r s hs R hr n (strictNullHomotopy n)
    ⟨Classical.choose hex, (Classical.choose_spec hex).2⟩

/-- 選んだ族は単体の射影として厳密に整合する。 -/
lemma strictNullHomotopy_comp (n : ℕ) :
    (strictNullHomotopy X p r s hs R hr (n + 1)).val.map ≫ (p n).right =
      (strictNullHomotopy X p r s hs R hr n).val.map := by
  dsimp only [strictNullHomotopy]
  exact (Classical.choose_spec (exists_next_nullHomotopy X p r s hs R hr n
    (strictNullHomotopy X p r s hs R hr n))).1

/-- lim¹ の零障害から、厳密に整合する零ホモトピーを構成する。 -/
theorem exists_compatible_nullHomotopies
    (hz : nullHomotopyObstruction X p r s hs R = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) :
    ∃ U : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)),
      ∀ n, (U (n + 1)).map ≫ (p n).right = (U n).map := by
  obtain ⟨R', hR'⟩ := exists_zero_difference_family X p r s hs R hz
  have hr' (n : ℕ) : nullHomotopyDifferenceFamily X p r s hs R' n = 1 :=
    congrFun hR' n
  exact ⟨fun n ↦ (strictNullHomotopy X p r s hs R' hr' n).val,
    strictNullHomotopy_comp X p r s hs R' hr'⟩

end PointedFibrationTower
end
end SerrePositivity.KST.Spectra
