module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianCancellation
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.Core.PrismContraction

/-!
概要：cocartesian な垂直辺を持つホモトピーは始点側の cocartesian な辺を終点側でも保つ。
方針：正方形を二つの三角形に分け、合成と消去を順に適用する。
規約：底は quasicategory、射は inner fibration。
使われ方：最終 fiber への cocartesian な輸送の辺の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：正方形の二つの三角形の外側の面を四辺として計算する。
方針：Yoneda の下で二つの有限頂点写像を比較する。
規約：第一座標が時刻、第二座標が辺のパラメータ。
使われ方：ホモトピーの四辺の cocartesian 性。 -/
lemma kanSquareTriangle_outerFaces :
    (stdSimplex.δ (2 : Fin 3) ≫ squareTriangle.{u} 0 = prismEndpoint 0 Δ[1]) ∧
    (stdSimplex.δ (0 : Fin 3) ≫ squareTriangle.{u} 0 =
      lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) ∧
    (stdSimplex.δ (2 : Fin 3) ≫ squareTriangle.{u} 1 =
      lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) ∧
    (stdSimplex.δ (0 : Fin 3) ≫ squareTriangle.{u} 1 = prismEndpoint 1 Δ[1]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

/-- 概要：正方形の始点側と両垂直辺が cocartesian なら終点側も cocartesian。
方針：一つ目の三角形で対角の合成性、二つ目で消去を使う。
規約：辺の性質は同じ射 p に関するもの。
使われ方：cocartesian なホモトピーに沿う辺の輸送。 -/
lemma kanCocartesianSquare_target {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
    (h₀ : IsCocartesianEdge p (SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ F)))
    (hx : IsCocartesianEdge p (SSet.yonedaEquiv
      (lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ F)))
    (hy : IsCocartesianEdge p (SSet.yonedaEquiv
      (lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ F))) :
    IsCocartesianEdge p (SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ F)) := by
  obtain ⟨h00, h01, h10, h11⟩ := kanSquareTriangle_outerFaces.{u}
  have hd := isCocartesianEdge_triangle_longEdge (squareTriangle 0 ≫ F) p
    (by simpa only [← Category.assoc, h00] using h₀)
    (by simpa only [← Category.assoc, h01] using hy)
  have h := kanIsCocartesianEdge_triangle_second_of_first_long (squareTriangle 1 ≫ F) p
    (by simpa only [← Category.assoc, h10] using hx)
    (by simpa only [← Category.assoc, squareTriangle_diagonal] using hd)
  simpa only [← Category.assoc, h11] using h

/-- 概要：cocartesian な垂直辺を持つホモトピーは始点側の cocartesian な辺を終点側へ移す。
方針：指定された辺でホモトピーを制限して正方形の消去を使う。
規約：パラメータ A の quasicategory 性は不要。
使われ方：最終 fiber への retraction の辺の性質。 -/
lemma kanCocartesianHomotopy_targetEdge {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (f : (Δ[1] : SSet.{u}) ⟶ A)
    (h₀ : IsCocartesianEdge p (SSet.yonedaEquiv (f ≫ prismEndpoint 0 A ≫ H)))
    (hv : ∀ x : A _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) :
    IsCocartesianEdge p (SSet.yonedaEquiv (f ≫ prismEndpoint 1 A ≫ H)) := by
  have hside (j : Fin 2) :
      (lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm j)) ≫
        (Δ[1] ◁ f)) ≫ H =
      lift (𝟙 Δ[1]) (SSet.const (f.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm j))) ≫ H := by
    rw [lift_whiskerLeft, SSet.const_comp]
  have h := kanCocartesianSquare_target p ((Δ[1] ◁ f) ≫ H)
    (by
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
      exact h₀)
    (by
      rw [← Category.assoc, hside]
      exact hv (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (by
      rw [← Category.assoc, hside]
      exact hv (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc] at h
  exact h

end SerrePositivity.InfinityCategories
