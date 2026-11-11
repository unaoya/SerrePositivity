module

public import SerrePositivity.KST.Spectra.TowerHomotopyTriangleStep

/-!
概要：隣接差の族が等しい球面の二つの塔の間に、厳密に整合する相対ホモトピーを作る。
方針：各段に三角形の充填を保持し、前段の相対ホモトピーを厳密に射影する次段を選ぶ。
規約：両端の球面と二つの零ホモトピーの族は固定する。
使われ方：Goerss–Jardine VIII §1。核の障害の単射性への幾何的な入力。
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

/-- 相対ホモトピーと、両側の零ホモトピーを三辺とする三角形。 -/
structure HomotopyTriangle {X : SSet.{u}} {x : X _⦋0⦌} {r : ℕ}
    {s t : X.PtSimplex (r + 1) x}
    (R : PtSimplex.RelStruct .const s (Fin.last (r + 1)))
    (S : PtSimplex.RelStruct .const t (Fin.last (r + 1))) where
  relation : PtSimplex.RelStruct s t (Fin.last (r + 1))
  filler : (Δ[r + 3] : SSet.{u}) ⟶ X
  face : ∀ j, stdSimplex.δ j ≫ filler = NullHomotopyTransport.triangleFace R relation S j

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)
  (s t : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
  (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (s (n + 1)) = s n)
  (ht : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (t (n + 1)) = t n)
  (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))
  (S : ∀ n, PtSimplex.RelStruct .const (t n) (Fin.last (r + 1)))
  (hd : nullHomotopyDifferenceFamily X p r s hs R = nullHomotopyDifferenceFamily X p r t ht S)

include hd in
/-- 前段の相対ホモトピーを厳密に射影する三角形の次段がある。 -/
lemma exists_next_triangle (n : ℕ) (U : HomotopyTriangle (R n) (S n)) :
    ∃ V : HomotopyTriangle (R (n + 1)) (S (n + 1)),
      V.relation.map ≫ (p n).right = U.relation.map := by
  obtain ⟨A, φ, hp, hφ⟩ := NullHomotopyTriangle.exists_step (p n).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (hs n) (ht n)
    (R n) (S n) (R (n + 1)) (S (n + 1)) U.relation U.filler U.face (congrFun hd n)
  exact ⟨⟨A, φ, hφ⟩, hp⟩

/-- 整合する相対ホモトピーを三角形と共に帰納的に選ぶ。 -/
def compatibleHomotopyTriangle : ∀ n, HomotopyTriangle (R n) (S n)
  | 0 =>
    let φ := (NullHomotopyTriangle.compatible (R 0) (S 0)).liftOfKanComplex
    let hφ j hj := (NullHomotopyTriangle.compatible (R 0) (S 0)).δ_liftOfKanComplex j hj
    ⟨NullHomotopyTriangle.relation (R 0) (S 0) φ hφ, φ,
      NullHomotopyTriangle.filler_face (R 0) (S 0) φ hφ⟩
  | n + 1 => Classical.choose (exists_next_triangle X p r s t hs ht R S hd n
      (compatibleHomotopyTriangle n))

/-- 選んだ相対ホモトピーは、各段の射影と厳密に可換。 -/
lemma compatibleHomotopyTriangle_comp (n : ℕ) :
    (compatibleHomotopyTriangle X p r s t hs ht R S hd (n + 1)).relation.map ≫ (p n).right =
      (compatibleHomotopyTriangle X p r s t hs ht R S hd n).relation.map :=
  Classical.choose_spec (exists_next_triangle X p r s t hs ht R S hd n
    (compatibleHomotopyTriangle X p r s t hs ht R S hd n))

include hd in
/-- 等しい隣接差の族から、厳密に整合する相対ホモトピーの族が得られる。 -/
theorem exists_compatible_relStruct_of_differenceFamily_eq :
    ∃ A : ∀ n, PtSimplex.RelStruct (s n) (t n) (Fin.last (r + 1)),
      ∀ n, (A (n + 1)).map ≫ (p n).right = (A n).map :=
  ⟨fun n ↦ (compatibleHomotopyTriangle X p r s t hs ht R S hd n).relation,
    compatibleHomotopyTriangle_comp X p r s t hs ht R S hd⟩

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
