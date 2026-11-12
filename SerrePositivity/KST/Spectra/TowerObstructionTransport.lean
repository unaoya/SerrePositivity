module

public import SerrePositivity.KST.Spectra.NullTransportDifference
public import SerrePositivity.KST.Spectra.TowerNullHomotopyObstruction

/-!
概要：塔で整合する球面の相対ホモトピーは lim¹ 障害を保つ。
方針：各段で零ホモトピーを移送し、射影した充填を比較ホーンへ渡す。
規約：各段の Kan 充填の厳密な自然性を要求せず、任意の充填の差の式を使う。
使われ方：Goerss–Jardine VIII §1。核の球面代表から類への降下。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NullHomotopyDifference NullHomotopyTransport

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] (r : ℕ)
  (s t : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
  (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (s (n + 1)) = s n)
  (ht : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (t (n + 1)) = t n)
  (A : ∀ n, PtSimplex.RelStruct (s n) (t n) (Fin.last (r + 1)))
  (hc : ∀ n, (A (n + 1)).map ≫ (p n).right = (A n).map)
  (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))

include hc in
/-- 移送した零ホモトピーの差の族は元の差の族と等しい。 -/
lemma nullHomotopyDifferenceFamily_transport :
    nullHomotopyDifferenceFamily X p r s hs R =
      nullHomotopyDifferenceFamily X p r t ht (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport (R n) (A n)) := by
  funext n
  apply difference_eq_of_transport_fillers (R n)
    (mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (R (n + 1)))
    (A n) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport (R n) (A n))
    (mapNullTo (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (ht n)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport (R (n + 1)) (A (n + 1))))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible (R n) (A n)).liftOfKanComplex
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible (R (n + 1)) (A (n + 1))).liftOfKanComplex ≫ (p n).right)
  · intro j
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.filler_face (R n) (A n) j
  · intro j
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.filler_face]
    dsimp only [triangleFace]
    split_ifs
    · exact (mapNullTo_map _ _ _ _).symm
    · exact (mapNullTo_map _ _ _ _).symm
    · exact hc n
    · rw [const_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint]

include hc in
/-- 相対ホモトピーに沿う移送は lim¹ の障害を保つ。 -/
theorem nullHomotopyObstruction_transport :
    nullHomotopyObstruction X p r s hs R =
      nullHomotopyObstruction X p r t ht (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport (R n) (A n)) :=
  congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _) (nullHomotopyDifferenceFamily_transport X p r s t hs ht A hc R)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
