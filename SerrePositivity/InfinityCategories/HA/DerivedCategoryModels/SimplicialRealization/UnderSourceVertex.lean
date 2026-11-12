module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SourceVertexSimplex
public import SerrePositivity.HomologicalAlgebra.UnderNerveWeight
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SourceVertexSimplex
import all SerrePositivity.HomologicalAlgebra.UnderNerveWeight

/-!
# under bar 重みから標準単体の重みへの同じ先頭頂点写像

## 概要
under 圏の射列の先頭頂点単体を、その構造射で元の標準単体へ戻す。

## 方針
先頭頂点単体の全自然性と under の可換三角形を合成する。

## 規約
Δᵒᵖ とその二重 opposite の向きを明記し、元の全射列の作用素を保持する。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。実際の bar／標準単体の重みの比較と指定増大の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization

/-- under の先頭の構造射で戻した、同じ先頭頂点単体の作用素。 -/
def underSourceVertex {x : SimplexCategoryᵒᵖ} {n : ℕ}
    (τ : ComposableArrows (Under x) n) : x ⟶ op (SimplexCategory.mk n) :=
  (sourceVertexSimplex (τ ⋙ Under.forget x) ≫ (τ.obj 0).hom.unop).op

/-- 底の前合成は、元の先頭頂点作用素の前合成と厳密に一致する。 -/
theorem underSourceVertex_map {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) {n : ℕ}
    (τ : ComposableArrows (Under y) n) :
    underSourceVertex (τ ⋙ Under.map f) = f ≫ underSourceVertex τ := by
  apply Quiver.Hom.unop_inj
  change sourceVertexSimplex (τ ⋙ Under.forget y) ≫ ((τ.obj 0).hom.unop ≫ f.unop) =
    (sourceVertexSimplex (τ ⋙ Under.forget y) ≫ (τ.obj 0).hom.unop) ≫ f.unop
  exact (Category.assoc _ _ _).symm

/-- 任意の単体作用素で引き戻しても、元の同じ作用素の後合成となる。 -/
theorem underSourceVertex_whisker {x : SimplexCategoryᵒᵖ} {m n : ℕ}
    (τ : ComposableArrows (Under x) n)
    (r : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    underSourceVertex ((SimplexCategory.toCat.map r).toFunctor ⋙ τ) =
      underSourceVertex τ ≫ r.op := by
  apply Quiver.Hom.unop_inj
  change sourceVertexSimplex ((SimplexCategory.toCat.map r).toFunctor ⋙
      (τ ⋙ Under.forget x)) ≫ (τ.obj (r.toOrderHom 0)).hom.unop =
    r ≫ sourceVertexSimplex (τ ⋙ Under.forget x) ≫ (τ.obj 0).hom.unop
  have hτ := (τ.map (homOfLE (Fin.zero_le (r.toOrderHom 0)))).w
  rw [← hτ, unop_comp, ← Category.assoc]
  exact (congrArg (fun f => f ≫ (τ.obj 0).hom.unop)
    (sourceVertexSimplex_whisker (τ ⋙ Under.forget x) r)).trans (Category.assoc _ _ _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
