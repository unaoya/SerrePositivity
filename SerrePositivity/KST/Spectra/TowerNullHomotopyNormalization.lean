module

public import SerrePositivity.KST.Spectra.NullDifferenceRealization
public import SerrePositivity.KST.Spectra.TowerNullHomotopyObstruction

/-!
概要：lim¹ 障害が零なら、隣接する差が全て零となる零ホモトピーの族を選べる。
方針：単位軌道への twisted 作用を商の等式から取り出し、各作用の類を差として実現する。
規約：この段階では零の差を得る。厳密な整合性は相対持ち上げで別に作る。
使われ方：Goerss–Jardine VIII §1。零障害からの零ホモトピーの構成。
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

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] (r : ℕ)
  (s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
  (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (s (n + 1)) = s n)
  (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))

/-- 零の lim¹ 障害を、各段の差が零となる零ホモトピーの選択へ直す。 -/
theorem exists_zero_difference_family
    (hz : nullHomotopyObstruction X p r s hs R = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) :
    ∃ R' : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)),
      nullHomotopyDifferenceFamily X p r s hs R' = 1 := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _ (nullHomotopyDifferenceFamily X p r s hs R) =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _ 1 at hz
  obtain ⟨a, ha⟩ := Quotient.exact hz
  choose R' hR' using fun n ↦ exists_left_difference (R n) (a n)
  refine ⟨R', ?_⟩
  rw [nullHomotopyDifferenceFamily_change X p r s hs R R']
  have he : (fun n ↦ difference (R' n) (R n)) = a := funext hR'
  rw [he]
  exact ha

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
