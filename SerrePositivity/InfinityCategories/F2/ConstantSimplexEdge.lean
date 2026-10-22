module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
概要：一単体の両端への定値引き戻しは、元の端点の同じ退化辺。
方針：定値順序射を退化と面の合成で表し、自然性でその像も回収する。
規約：元の一単体・反転・端点を保持する。
使われ方：共通解像の消去式に残る二つの定値辺の類を除く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 一単体の端点への定値引き戻しは同じ元の端点の退化辺。 -/
lemma constantSimplexPullback_degenerate {X : SSet.{u}} (e : X _⦋1⦌) (j : Fin 2) :
    X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op e = X.σ 0 (X.δ j.rev e) := by
  have h : SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ j.rev =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ j := by
    fin_cases j <;> ext i <;> fin_cases i <;> rfl
  rw [← h]
  exact X.map_comp_apply (SimplexCategory.δ j.rev).op (SimplexCategory.σ (0 : Fin 1)).op e

/-- 反転後も元の同じ端点における退化辺を保持する。 -/
lemma oppositeConstantSimplexPullback_degenerate {X : SSet.{u}}
    (e : X _⦋1⦌) (j : Fin 2) :
    SSet.opObjEquiv.symm (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op e) =
      X.op.σ 0 (SSet.opObjEquiv.symm (X.δ j.rev e)) := by
  rw [constantSimplexPullback_degenerate, SSet.op_σ]
  rfl

/-- 同じ定値引き戻しの像は元の端点像の同じ退化辺。 -/
lemma constantSimplexPullback_image_degenerate {X Y : SSet.{u}} (f : X ⟶ Y)
    (e : X _⦋1⦌) (j : Fin 2) :
    f.app (Opposite.op ⦋1⦌) (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op e) =
      Y.σ 0 (f.app (Opposite.op ⦋0⦌) (X.δ j.rev e)) := by
  rw [constantSimplexPullback_degenerate]
  exact ConcreteCategory.congr_hom (f.naturality (SimplexCategory.σ (0 : Fin 1)).op)
    (X.δ j.rev e)

end SerrePositivity.InfinityCategories.F2
