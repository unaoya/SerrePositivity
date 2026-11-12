module

public import SerrePositivity.KST.Spectra.NullHomotopyEndpointLifting
public import SerrePositivity.KST.Spectra.NullDifferenceRealization
public import SerrePositivity.KST.Spectra.TowerNullHomotopyObstruction

/-!
概要：指定した高次の差を持つ、塔の球面と零ホモトピーの次段を構成する。
方針：前段で差を実現した零ホモトピーを、球面の終点と共に次段へ厳密に持ち上げる。
規約：次段の球面の射影と零ホモトピーの差を同時に指定する。
使われ方：Goerss–Jardine VIII §1。lim¹ の任意の代表の実現の帰納工程。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NullHomotopyDifference

/-- 球面とその指定した零ホモトピーの組。 -/
abbrev NullSphereStage (X : PointedSimplicialSet.{u}) (r : ℕ) :=
  Σ s : X.right.PtSimplex (r + 1) X.basepoint,
    PtSimplex.RelStruct .const s (Fin.last (r + 1))

/-- 指定した差を持つ次段は、球面を厳密に射影しながら構成できる。 -/
lemma exists_difference_step {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [KanComplex B.right] [Fibration p.right] {r : ℕ}
    (U : NullSphereStage B r) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right (r + 1) B.basepoint) :
    ∃ V : NullSphereStage E r,
      ∃ hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) V.1 = U.1,
        difference U.2 (mapNullTo p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) hs V.2) = a := by
  obtain ⟨T, hT⟩ := exists_difference U.2 a
  obtain ⟨t, S, hs, hS⟩ := NullHomotopyEndpointLifting.exists_lift p.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) T
  refine ⟨⟨t, S⟩, hs, ?_⟩
  have he : mapNullTo p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) hs S = T := by
    have hm := (mapNullTo_map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) hs S).trans hS
    generalize mapNullTo p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) hs S = A at hm ⊢
    cases A
    cases T
    cases hm
    rfl
  rw [he]
  exact hT

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
