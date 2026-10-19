module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransPinchedSource
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (C D : Type v) [DGCategory A C] [DGCategory A D]
variable {F G : DGFunctor A C D} (η : StrictNatTrans F G) (x : C)

/-- 自然変換の点上の実辺は、指定された閉零成分から作る実辺。 -/
lemma dgStrictNatTransPointMap_edge :
    dgStrictNatTransPointMap A C D η x =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm (edgeOfCycle (x := Simplex.vertex (F.obj x))
        (y := Simplex.vertex (G.obj x)) (η.app x)).edge := by
  apply SSet.yonedaEquiv.injective
  have h : (SSet.yonedaEquiv (X := dgNerve A D)) (dgStrictNatTransPointMap A C D η x) =
      (edgeOfCycle (x := Simplex.vertex (F.obj x))
        (y := Simplex.vertex (G.obj x)) (η.app x)).edge := by
    change η.simplex (PinchedHom.constant (X := dgNerve A C) (Simplex.vertex x) 1)
      OrderHom.id = (edgeOfCycle (x := Simplex.vertex (F.obj x))
        (y := Simplex.vertex (G.obj x)) (η.app x)).edge
    apply Simplex.edgeEquiv.injective
    refine Sigma.ext ?_ ?_
    · funext i
      fin_cases i <;> rfl
    · apply heq_of_eq
      apply Subtype.ext
      change compose A (η.app x).val ((F.map x x).f 0 (unitElement A x).val) (by decide) =
        (η.app x).val
      rw [DGFunctor.map_unitElement, compose_unit]
  exact h.trans (Equiv.apply_symm_apply _ _).symm

end SerrePositivity.InfinityCategories
