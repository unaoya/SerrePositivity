module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransPinchedSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

/-! # 自然変換の対象成分と元の実閉辺の一致

概要：厳密 dg 自然変換の指定対象上の一単体は、元の閉零成分の実辺そのもの。
方針：標準一単体の普遍性と、両端・唯一の次数零成分の評価を使う。
規約：元の一単体を選び直さない。使われ方：slice prism の始域を実細分辺へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (C D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {F G : DGFunctor A C D} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x : C)

/-- 自然変換の点上の実辺は、指定された閉零成分から作る実辺。 -/
lemma dgStrictNatTransPointMap_edge :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPointMap A C D η x =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj x)) (η.app x)).edge := by
  apply SSet.yonedaEquiv.injective
  have h : (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPointMap A C D η x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj x)) (η.app x)).edge := by
    change η.simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) 1)
      OrderHom.id = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj x)) (η.app x)).edge
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
    refine Sigma.ext ?_ ?_
    · funext i
      fin_cases i <;> rfl
    · apply heq_of_eq
      apply Subtype.ext
      change _root_.SerrePositivity.DifferentialGraded.compose A (η.app x).val ((F.map x x).f 0 (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val) (by decide) =
        (η.app x).val
      rw [_root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement, _root_.SerrePositivity.DifferentialGraded.compose_unit]
  exact h.trans (Equiv.apply_symm_apply _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
