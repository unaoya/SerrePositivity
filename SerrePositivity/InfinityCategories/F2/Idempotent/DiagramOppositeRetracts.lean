module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessOpposite
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorOppositeHom

/-!
概要：元の全図式の関手 ∞ 圏内の retract は、元の反転図式の全関手圏へ移る。
方針：同じ retract を反転し、元の内部 Hom の反転同型で写す。
規約：元の図式全体を厳密に反転する。成分ごとの retract だけで代用しない。
使われ方：全余極限・普遍四角形の retract 閉性の双対化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 同じ全図式の retract は、元の反転した全図式の関手 ∞ 圏内の retract となる。 -/
lemma diagram_retract_op {K X : SSet.{u}} [Quasicategory X] (a b : K ⟶ X)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (functorVertex a) (functorVertex b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (functorVertex (SSet.opFunctor.map a))
      (functorVertex (SSet.opFunctor.map b)) := by
  have h := r.op.map (HomotopyLimits.oppositeInternalHomIso K X).hom
  rwa [SerrePositivity.InfinityCategories.F1B.oppositeInternalHom_vertex, SerrePositivity.InfinityCategories.F1B.oppositeInternalHom_vertex] at h

end SerrePositivity.InfinityCategories.F2.Idempotent
