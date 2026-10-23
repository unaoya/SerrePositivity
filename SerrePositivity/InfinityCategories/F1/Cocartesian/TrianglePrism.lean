module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TrianglePrism

/-!
概要：三角形の prism の各頂点での cocartesian 合成性。
方針：パラメーターの頂点で三角形を評価し、辺の合成閉性を使う。
規約：標準一単体の恒等とパラメーターの定値一単体の組を垂直辺と呼ぶ。
使われ方：Kerodon Proposition 5.2.5.1、合成した transport の証人の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二辺が各頂点で cocartesian なら三角形の prism の長辺も各頂点で cocartesian。
方針：パラメーターの頂点を固定した標準二単体に合成閉性を適用する。
規約：底は quasicategory、射は inner fibration。
使われ方：Kerodon Proposition 5.2.5.1、transport 関手の合成の cocartesian 条件。 -/
lemma cocartesianTrianglePrism_longEdge {X B A : SSet.{u}} [Quasicategory B]
    (p : X ⟶ B) [InnerFibration p] (T : (Δ[2] : SSet.{u}) ⊗ A ⟶ X)
    (hfirst : ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (((stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)))
    (hsecond : ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (((stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ T).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)) := by
  intro v
  let tv : (Δ[2] : SSet.{u}) ⟶ X := lift (𝟙 _) (SSet.const v) ≫ T
  have hn (i : Fin 3) : stdSimplex.δ i ≫ tv =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const v) ≫ ((stdSimplex.δ i ▷ A) ≫ T) := by
    rfl
  have hf : IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ tv)) := by
    rw [hn]
    exact hfirst v
  have hs : IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ tv)) := by
    rw [hn]
    exact hsecond v
  have h := isCocartesianEdge_triangle_longEdge tv p hf hs
  rw [hn] at h
  exact h

end SerrePositivity.InfinityCategories
