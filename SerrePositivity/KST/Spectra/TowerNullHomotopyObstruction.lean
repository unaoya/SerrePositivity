module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceChange
public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceNaturality
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TowerLimOne

/-!
概要：整合する球面の段ごとの零ホモトピーから lim¹ の障害を作る。
方針：隣接する零ホモトピーの差を取り、選択変更を twisted 作用として計算する。
規約：ここでは球面の代表は固定する。ホモトピー類の代表変更と障害の完全性は別工程。
使われ方：Goerss–Jardine VIII §1。Milnor 比較の核からの障害写像。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NullHomotopyDifference

/-- 射影の像を指定した球面へ同定して零ホモトピーを移す。 -/
def mapNullTo {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌} {r : ℕ}
    (f : X ⟶ Y) (hf : f.app _ x = y)
    {s : X.PtSimplex (r + 1) x} {t : Y.PtSimplex (r + 1) y}
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f hf s = t) (R : PtSimplex.RelStruct .const s (Fin.last (r + 1))) :
    PtSimplex.RelStruct .const t (Fin.last (r + 1)) := ht ▸ mapNull f hf R

/-- 球面の同定は零ホモトピーの underlying な単体を変えない。 -/
lemma mapNullTo_map {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌} {r : ℕ}
    (f : X ⟶ Y) (hf : f.app _ x = y)
    {s : X.PtSimplex (r + 1) x} {t : Y.PtSimplex (r + 1) y}
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f hf s = t) (R : PtSimplex.RelStruct .const s (Fin.last (r + 1))) :
    (mapNullTo f hf ht R).map = R.map ≫ f := by
  subst t
  rfl

/-- 指定した球面への同定を含む差の自然性。 -/
lemma difference_map_to {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} {r : ℕ} (f : X ⟶ Y) (hf : f.app _ x = y)
    {s : X.PtSimplex (r + 1) x} {t : Y.PtSimplex (r + 1) y}
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f hf s = t) (R S : PtSimplex.RelStruct .const s (Fin.last (r + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf (difference R S) =
      difference (mapNullTo f hf ht R) (mapNullTo f hf ht S) := by
  subst t
  exact difference_map f hf R S

end NullHomotopyDifference

namespace PointedFibrationTower
open NullHomotopyDifference

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] (r : ℕ)
  (s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
  (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (s (n + 1)) = s n)

/-- 隣接する零ホモトピーの差の族。 -/
def nullHomotopyDifferenceFamily
    (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))
    (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint :=
  difference (R n) (mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (hs n) (R (n + 1)))

/-- 零ホモトピーの選択変更は差の族への twisted 作用になる。 -/
lemma nullHomotopyDifferenceFamily_change
    (R R' : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1))) :
    nullHomotopyDifferenceFamily X p r s hs R' =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
        (fun n ↦ pointedGroupMap (r + 1) (p n))
        (fun n ↦ difference (R' n) (R n)) (nullHomotopyDifferenceFamily X p r s hs R) := by
  funext n
  dsimp only [nullHomotopyDifferenceFamily, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist]
  rw [difference_change (R n)
    (mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (R (n + 1)))
    (R' n)
    (mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (R' (n + 1))),
    ← difference_map_to]
  rfl

/-- 段ごとの零ホモトピーから得られる lim¹ の障害。 -/
def nullHomotopyObstruction
    (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _ (nullHomotopyDifferenceFamily X p r s hs R)

/-- 固定した球面の族の lim¹ の障害は零ホモトピーの選択に依存しない。 -/
theorem nullHomotopyObstruction_eq
    (R R' : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1))) :
    nullHomotopyObstruction X p r s hs R = nullHomotopyObstruction X p r s hs R' := by
  unfold nullHomotopyObstruction
  rw [nullHomotopyDifferenceFamily_change X p r s hs R R']
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk_twist _ _ _ _

include hs in
/-- 厳密に整合する零ホモトピーがあれば、障害は lim¹ の基点。 -/
theorem nullHomotopyObstruction_eq_point_of_compatible
    (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))
    (hc : ∀ n, (R (n + 1)).map ≫ (p n).right = (R n).map) :
    nullHomotopyObstruction X p r s hs R = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  have he : nullHomotopyDifferenceFamily X p r s hs R = 1 := by
    funext n
    have hn : mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
        (hs n) (R (n + 1)) = R n := by
      have he := (mapNullTo_map (p n).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (R (n + 1))).trans (hc n)
      generalize mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
        (hs n) (R (n + 1)) = a at he ⊢
      generalize R n = b at he ⊢
      cases a
      cases b
      cases he
      rfl
    dsimp only [nullHomotopyDifferenceFamily]
    rw [hn, difference_self]
    rfl
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _) he

end PointedFibrationTower
end
end SerrePositivity.KST.Spectra
