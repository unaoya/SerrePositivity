module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeFunctorVertexIsoProjection
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecomposition

/-!
概要：相対関手空間の指定同型を元の全族へ写す作用は、前合成と端点の等号を保持する。
方針：元の fiber の包含と全前合成の可換性を、同じ頂点同型の像で照合する。
規約：相対比較の指定値と元の両全族を保持する。
使われ方：終点面の底固定比較を、旧族での元の指定全族の比較へ戻す。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：相対比較を元の全族へ写す作用は、元の前合成と厳密に可換。
方針：元の二つの包含の合成を照合。規約：同じ指定同型。使われ方：旧族の比較回収。 -/
lemma relativeFunctorVertexIsoImage_precomp {A A₀ E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (f g : A ⟶ E)
    (hf : f ≫ p = b) (hg : g ≫ p = b)
    (e : VertexIso (relativeFunctorVertex p b f hf) (relativeFunctorVertex p b g hg))
    (j : A₀ ⟶ A) :
    (relativeFunctorVertexIsoImage p b f g hf hg e).precomp j =
    relativeFunctorVertexIsoImage p (j ≫ b) (j ≫ f) (j ≫ g)
      (by rw [Category.assoc, hf]) (by rw [Category.assoc, hg])
      (VertexIso.map e (relativeFunctorPre p b j)) := by
  change VertexIso.map (VertexIso.map e (vertexFiberι ((ihom A).map p) (functorVertex b)))
      ((pre j).app E) =
    VertexIso.map (VertexIso.map e (relativeFunctorPre p b j))
      (vertexFiberι ((ihom A₀).map p) (functorVertex (j ≫ b)))
  rw [VertexIso.map_comp, VertexIso.map_comp]
  rfl
/-- 概要：同じ相対比較の端点を等号で表示変更しても、元の全族で同じ指定同型を保持。
方針：元の両端の等号を消去。規約：同じ指定値。使われ方：相対自然性の全族への帰還。 -/
lemma relativeFunctorVertexIsoImage_heq {A E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (f g f' g' : A ⟶ E) (hf : f ≫ p = b) (hg : g ≫ p = b)
    (hf' : f' ≫ p = b) (hg' : g' ≫ p = b)
    (e : VertexIso (relativeFunctorVertex p b f hf) (relativeFunctorVertex p b g hg))
    (e' : VertexIso (relativeFunctorVertex p b f' hf') (relativeFunctorVertex p b g' hg'))
    (hff : f = f') (hgg : g = g') (he : HEq e e') :
    HEq (relativeFunctorVertexIsoImage p b f g hf hg e)
      (relativeFunctorVertexIsoImage p b f' g' hf' hg' e') := by
  subst f'
  subst g'
  cases eq_of_heq he
  rfl
end SerrePositivity.InfinityCategories.F2.Ind
