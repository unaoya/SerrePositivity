module

public import SerrePositivity.InfinityCategories.F2.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.F1.PullbackTransport
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberValue

/-!
概要：元の unstraightening の輸送と、同じ図式の辺の Kan 値の作用を全自然比較する。
方針：引き戻し fiber 同型で普遍輸送へ戻し、元の pointed fiber 値比較を合成する。
規約：元の図式・指定辺・選択済みの値同値を保つ。
使われ方：共変 Hom の分類図式の作用を元の coslice 輸送へ照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ辺に沿う unstraightening の実輸送と、元の図式の Kan 値の作用の全自然比較。 -/
def unstraighteningValueTransportIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : B.Edge a b) :
    FunctorIso (edgeTransport (leftUnstraighteningProjection F) e ≫
      (leftUnstraighteningFiberValueEquivalence F b).hom)
      ((leftUnstraighteningFiberValueEquivalence F a).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (e.map F))) := by
  have h := (edgeTransport_pullbackIso pointedSpaceProjection F e).precomp
    (leftUnstraighteningFiberIso F a).hom
  have h' : FunctorIso (edgeTransport (leftUnstraighteningProjection F) e ≫
      (leftUnstraighteningFiberIso F b).hom)
      ((leftUnstraighteningFiberIso F a).hom ≫
        edgeTransport pointedSpaceProjection (e.map F)) := by
    simpa only [Category.assoc, leftUnstraighteningFiberIso,
      leftUnstraighteningProjection, Iso.hom_inv_id_assoc] using h
  have k := h'.postcomp (pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) b)).hom
  have l := FunctorIso.precomp (spaceInfinityEdgeTransportValueIso (e.map F)).symm
    (leftUnstraighteningFiberIso F a).hom
  simp only [Category.assoc] at k l
  simpa only [leftUnstraighteningFiberValueEquivalence, QCatEquivalence.trans,
    qCatEquivalenceOfIso, Category.assoc] using k ≪≫ l

end SerrePositivity.InfinityCategories.F2.Compact
