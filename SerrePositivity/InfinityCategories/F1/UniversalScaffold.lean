module

public import SerrePositivity.InfinityCategories.F1.UniversalScaffoldEvaluation

/-!
概要：strict transport の simplicial replacement から元の全空間への universal scaffold の射。
方針：undercategory の標準単体における係数の対角評価を全次数で束縛する。
規約：単体集合の射と底上の可換性を構成し、全空間の同値は後続で扱う。
使われ方：Kerodon Construction 5.3.4.7、strict transport からの復元の比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：strict transport の simplicial replacement から元の全空間への評価射。
方針：対角評価の自然性を使って次数ごとの評価を単体集合の射にする。
規約：構成自体に p の left fibration 性は要求しない。
使われ方：Kerodon Construction 5.3.4.7、元の全空間との比較の片側の射。 -/
def universalScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : simplicialReplacement (leftStrictTransportDiagram p) ⟶ E where
  app _ := ↾fun s ↦ SSet.yonedaEquiv (universalScaffoldSimplex p s)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    change SSet.yonedaEquiv (universalScaffoldSimplex p
      (simplicialReplacementSimplexMap (leftStrictTransportDiagram p) α.unop s)) =
      E.map α (SSet.yonedaEquiv (universalScaffoldSimplex p s))
    rw [universalScaffoldSimplex_naturality]
    exact (SSet.yonedaEquiv_naturality α.unop (universalScaffoldSimplex p s)).symm

/-- 概要：universal scaffold は底の nerve 上の射。
方針：単体評価の底への合成の公式を Yoneda の自然性で各次数へ移す。
規約：元の射影 p と simplicial replacement の射影を厳密に固定する。
使われ方：Kerodon Proposition 5.3.4.8、scaffold の底に関する条件。 -/
lemma universalScaffold_projection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) :
    universalScaffold p ≫ p = simplicialReplacementProjection (leftStrictTransportDiagram p) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  change p.app d (SSet.yonedaEquiv (universalScaffoldSimplex p s)) = s.1
  rw [← SSet.yonedaEquiv_comp, universalScaffoldSimplex_projection]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories
