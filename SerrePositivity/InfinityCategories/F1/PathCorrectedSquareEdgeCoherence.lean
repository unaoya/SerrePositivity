module

public import SerrePositivity.InfinityCategories.F1.EquivalencePathFamilyEdge
public import SerrePositivity.InfinityCategories.F1.PathCorrectedFunctorSquare

/-!
概要：補正成分の全 path の像は、元の自然性を表す同じ辺を厳密に回収する。
方針：path の関手空間の辺への復元を後合成と可換にし、指定 path の等式を使う。
規約：ホモトピー類だけでなく一単体そのものを照合する。
使われ方：元の分類 Hom 作用と補正 pullback 比較の coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ区間族の転置は、元の標的への後合成と厳密に可換。 -/
lemma transposeFunctorFamily_post {A I X Y : SSet.{u}}
    (F : A ⟶ (ihom I).obj X) (q : X ⟶ Y) :
    transposeFunctorFamily (F ≫ (ihom I).map q) =
      transposeFunctorFamily F ≫ (ihom A).map q := by
  apply uncurry_injective
  simp only [transposeFunctorFamily, uncurry_curry, uncurry_natural_right, Category.assoc]

/-- 全 path の同じ関手空間の辺は、path の後合成と厳密に可換。 -/
lemma equivalencePathFamilyEdge_post {A X Y : SSet.{u}}
    (L : A ⟶ equivalencePath X) (q : X ⟶ Y) :
    ((ihom A).map q).app (Opposite.op ⦋1⦌) (equivalencePathFamilyEdge L).edge =
      (equivalencePathFamilyEdge (L ≫ equivalencePathMap q)).edge := by
  rw [equivalencePathFamilyEdge_yoneda, equivalencePathFamilyEdge_yoneda]
  have h : (L ≫ equivalencePathMap q) ≫ equivalencePathι Y =
      (L ≫ equivalencePathι X) ≫ (ihom (Δ[1] : SSet.{u})).map q := by
    rw [Category.assoc, equivalencePathMap_ι, Category.assoc]
  rw [h, transposeFunctorFamily_post]
  exact (SSet.yonedaEquiv_comp _ _).symm

/-- 補正成分の持ち上げた path の像は、元の自然性を表す指定辺そのもの。 -/
lemma PathCorrectedFunctorSquare.path_edge_over {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B}
    {e : FunctorIso g (f ≫ q)} (s : PathCorrectedFunctorSquare q f g e) :
    ((ihom A).map q).app (Opposite.op ⦋1⦌) (equivalencePathFamilyEdge s.path).edge =
      (FunctorIso.edge e).edge := by
  have h := equivalencePathFamilyEdge_post s.path q
  rw [s.over] at h
  exact h.trans (equivalencePathFamilyEdge_of_invertible _ _)

end SerrePositivity.InfinityCategories
