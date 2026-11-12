module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTargetVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection

/-!
概要：定値相対 Hom の元の値への作用を、同じ実射の頂点で計算する。
方針：fiber 射影の頂点式に元の fiber の値への比較を続ける。
規約：元の実射と指定射影を保持。使われ方：下面の輸送因子の端点表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対実射の元の値への像は、同じ実射・fiber 射影・値への比較の合成の頂点。 -/
lemma constantUnstraighteningRelativeIso_value_vertex {A B : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (f : A ⟶ leftUnstraightening (SSet.const z : B ⟶ SpaceInfinity))
    (hf : f ≫ leftUnstraighteningProjection (SSet.const z) = a) :
    ((constantUnstraighteningRelativeIso a z).hom ≫
      (ihom A).map (pointedSpaceFiberValueEquivalence z).hom).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z)) a f hf) =
      functorVertex (f ≫ constantUnstraighteningFiberProjection B z ≫
        (pointedSpaceFiberValueEquivalence z).hom) := by
  change ((ihom A).map (pointedSpaceFiberValueEquivalence z).hom).app _
    ((constantUnstraighteningRelativeIso a z).hom.app _ _) = _
  rw [constantUnstraighteningRelativeIso_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2
