module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：prism の指定した係数頂点での評価を、形状・係数・底の射に同時に自然に計算する。
方針：形状の恒等射と係数の定値射を直積へ組み合わせる。
規約：prism を選び直さず、同じ raw な射を評価する。
使われ方：標準輸送の三角形 prism から、全空間の実際の三角形を取り出す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 同じ prism を、指定した係数の頂点で評価する。 -/
def prismVertexEvaluation {K A E : SSet.{u}} (W : K ⊗ A ⟶ E) (v : A _⦋0⦌) : K ⟶ E :=
  lift (𝟙 K) (SSet.const v) ≫ W

/-- 係数頂点の評価は、形状への前合成と厳密に可換。 -/
lemma prismVertexEvaluation_shape {K L A E : SSet.{u}}
    (W : K ⊗ A ⟶ E) (v : A _⦋0⦌) (j : L ⟶ K) :
    j ≫ prismVertexEvaluation W v = prismVertexEvaluation ((j ▷ A) ≫ W) v := by
  simp only [prismVertexEvaluation, ← Category.assoc, comp_lift, lift_whiskerRight,
    Category.comp_id, Category.id_comp, SSet.comp_const]

/-- 係数の射を先に適用しても、同じ像の頂点での評価になる。 -/
lemma prismVertexEvaluation_coefficient {K A A' E : SSet.{u}}
    (W : K ⊗ A' ⟶ E) (v : A _⦋0⦌) (f : A ⟶ A') :
    prismVertexEvaluation ((K ◁ f) ≫ W) v =
      prismVertexEvaluation W (f.app (Opposite.op ⦋0⦌) v) := by
  simp only [prismVertexEvaluation, ← Category.assoc, lift_whiskerLeft,
    SSet.const_comp]

/-- 評価した prism も、元の底の図式そのものを被覆する。 -/
lemma prismVertexEvaluation_projection {K A E B : SSet.{u}}
    (p : E ⟶ B) (W : K ⊗ A ⟶ E) (β : K ⟶ B)
    (hW : W ≫ p = fst K A ≫ β) (v : A _⦋0⦌) :
    prismVertexEvaluation W v ≫ p = β := by
  rw [prismVertexEvaluation, Category.assoc, hW, ← Category.assoc, lift_fst, Category.id_comp]

/-- 標準単体の頂点での制限は、同じ prism の頂点包含での評価と一致する。 -/
lemma prismVertexEvaluation_vertex {n : ℕ} {A E : SSet.{u}}
    (W : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) (v : A _⦋0⦌) (j : Fin (n + 1)) :
    SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm j) ≫ prismVertexEvaluation W v =
      SSet.yonedaEquiv.symm v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n j A ≫ W := by
  simp only [prismVertexEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex, SSet.yonedaEquiv_symm_zero,
    ← Category.assoc, comp_lift, Category.comp_id, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
