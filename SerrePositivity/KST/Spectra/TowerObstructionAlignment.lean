module

public import SerrePositivity.KST.Spectra.TowerNullHomotopyNormalization

/-!
概要：二つの等しい lim¹ 障害を、厳密に等しい隣接差の族に直す。
方針：軌道の等式の twisted 作用を、各段の零ホモトピーの選択変更で実現する。
規約：二つの球面の族は別でもよい。相対ホモトピーの存在はここでは要求しない。
使われ方：Goerss–Jardine VIII §1。核の障害の単射性の正規化。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NullHomotopyDifference

/-- 同じ障害の零ホモトピーは、隣接差の族が厳密に等しくなるよう選び直せる。 -/
theorem exists_equal_difference_family
    (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
    [∀ n, KanComplex (X n).right] (r : ℕ)
    (s t : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
    (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
      (s (n + 1)) = s n)
    (ht : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
      (t (n + 1)) = t n)
    (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))
    (S : ∀ n, PtSimplex.RelStruct .const (t n) (Fin.last (r + 1)))
    (he : nullHomotopyObstruction X p r s hs R = nullHomotopyObstruction X p r t ht S) :
    ∃ R' : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)),
      nullHomotopyDifferenceFamily X p r s hs R' = nullHomotopyDifferenceFamily X p r t ht S := by
  obtain ⟨a, ha⟩ := Quotient.exact he
  choose R' hR' using fun n ↦ exists_left_difference (R n) (a n)
  refine ⟨R', ?_⟩
  rw [nullHomotopyDifferenceFamily_change X p r s hs R R']
  have he' : (fun n ↦ difference (R' n) (R n)) = a := funext hR'
  rw [he']
  exact ha

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
