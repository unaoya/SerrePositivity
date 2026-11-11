module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoTwoEdgeValueReindex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTargetFiberTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoWhiskerVertexMap
public import
SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
/-!
概要：元の中間比較と辺値を後合成しても、同じ指定合成値と内部 Hom の像を保持する。
方針：元の三端点と指定値を保持し、後合成の結合と表示変更を合成する。
規約：元の辺値・中間比較と全初期係数を保持する。
使われ方：第一辺値を元の最後射へ写し、元の二辺評価を貼り合わせる。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
/-- 概要：元の中間比較と後合成した辺値は、同じ辺値合成の後合成。
方針：同じ三端点を保持して後合成と表示変更を交換する。
規約：元の指定値を保持。使われ方：第一辺値の最後射への像。 -/
lemma functorIsoEdgeValuePostAt_comp_heq {A B X Y Z K : SSet.{u}}
    (a : A ⟶ B) (v₀ : A ⟶ X) (v₁ : B ⟶ Y) (f : X ⟶ Y)
    (e : FunctorIso (a ≫ v₁) (v₀ ≫ f)) (q : K ⟶ A) (g : Y ⟶ Z)
    (p : K ⟶ B) (I : FunctorIso p (q ≫ a)) :
    HEq (I.postcomp (v₁ ≫ g) ≪≫ functorIsoEdgeValuePostAt a v₀ v₁ f e q g)
      (FunctorIso.postcomp (I.postcomp v₁ ≪≫ functorIsoEdgeValueAt a v₀ v₁ f e q) g) := by
  have hI := heq_of_eq (functorIso_postcomp_postcomp I v₁ g).symm
  have hF : HEq (functorIsoEdgeValuePostAt a v₀ v₁ f e q g)
      ((functorIsoEdgeValueAt a v₀ v₁ f e q).postcomp g) :=
    (functorIsoOfEq_heq _ _ _).trans
      (functorIsoOfEq_postcomp_heq (e.precomp q) (Category.assoc q a v₁).symm rfl g).symm
  have h := vertexIso_trans_heq_of_heq _ _ _ _
    (congrArg functorVertex (Category.assoc p v₁ g).symm)
    (congrArg functorVertex (Category.assoc (q ≫ a) v₁ g).symm)
    (congrArg functorVertex (by simp only [Category.assoc])) hI hF
  exact h.trans (heq_of_eq (functorIso_postcomp_trans (I.postcomp v₁)
    (functorIsoEdgeValueAt a v₀ v₁ f e q) g)).symm
/-- 概要：同じ実両端で照合した比較の後合成は元の内部 Hom 作用の像。
方針：明示した二頂点と同じ指定比較を後合成する。
規約：元の指定値を保持。使われ方：第一射の評価比較の最後射への像。 -/
lemma functorIso_postcomp_heq_vertexMap_of_heq {A Y Z : SSet.{u}} {f g : A ⟶ Y}
    (E : FunctorIso f g) {a b : ((ihom A).obj Y) _⦋0⦌} (D : VertexIso a b)
    (ha : functorVertex f = a) (hb : functorVertex g = b) (hE : HEq E D) (q : Y ⟶ Z) :
    HEq (E.postcomp q) (VertexIso.map D ((ihom A).map q)) :=
  (functorIso_postcomp_vertexMap_heq E q).trans
    (vertexIso_map_heq_of_heq E D ha hb hE ((ihom A).map q))
end
end SerrePositivity.InfinityCategories.F2
