module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.EdgeHom
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyRepresentative

/-!
概要：通常の自然変換と指定錐の後合成を実際のホモトピーへ移す。
方針：nerve の指数比較の辺を uncurry して成分を計算する。
規約：元の図式と自然変換を保ち、可逆性を仮定しない。
使われ方：B5 の指定単位・余単位の局所錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G : C ⥤ D}


/-- 概要：自然変換を指定された nerve 関手間の辺として表す。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
def nerveNatTransEdge (η : F ⟶ G) :
    Edge (functorVertex (nerveMap F)) (functorVertex (nerveMap G)) where
  edge := ((nerve.edgeMk η).map (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso C D).hom).edge
  src_eq := ((nerve.edgeMk η).map (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso C D).hom).src_eq.trans
    (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_vertex F)
  tgt_eq := ((nerve.edgeMk η).map (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso C D).hom).tgt_eq.trans
    (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_vertex G)

/-- 概要：自然変換を指定された nerve 関手間の実ホモトピーとして表す。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
def nerveNatTransHomotopy (η : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) :=
  simplicialHomotopyOfFunctorEdge (nerveNatTransEdge η).toTruncated

/-- 概要：具体的な辺の類は元の自然変換の h Fun 表示に等しい。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransEdge_hom (η : F ⟶ G) :
    HomotopyCategory.homMk (nerveNatTransEdge η) = SerrePositivity.InfinityCategories.F1B.nerveNatTransHom η := by
  symm
  exact SerrePositivity.InfinityCategories.F1B.homMk_congr (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_vertex F)
    (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_vertex G) _ _ rfl

/-- 概要：ホモトピーからの辺は元の具体的な辺を回収する。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_edge (η : F ⟶ G) :
    functorEdgeOfSimplicialHomotopy (nerveNatTransHomotopy η) =
      (nerveNatTransEdge η).toTruncated := by
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv
    (curry (uncurry (SSet.yonedaEquiv.symm (nerveNatTransEdge η).edge))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]
  rfl

/-- 概要：具体的なホモトピーは指定された自然変換の類を表す。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_hom (η : F ⟶ G) :
    HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (nerveNatTransHomotopy η)) =
      SerrePositivity.InfinityCategories.F1B.nerveNatTransHom η := by
  rw [nerveNatTransHomotopy_edge]
  exact nerveNatTransEdge_hom η

end SerrePositivity.InfinityCategories.F1B
