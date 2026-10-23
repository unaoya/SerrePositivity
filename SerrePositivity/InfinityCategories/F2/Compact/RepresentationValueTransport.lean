module

public import SerrePositivity.InfinityCategories.F2.Compact.UnstraighteningValueTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTransportNaturality

/-!
概要：元の left transport 表現の同じ fiber 比較は、元の輸送と Kan 値の作用に自然。
方針：実際の底上の比較による輸送自然性と、unstraightening の値比較を合成する。
規約：元の表現・比較射・辺と fiber 同値を保つ。
使われ方：compact 対象の Hom の脚の作用を、元の coslice の実輸送へ照合する。
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
variable {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]

/-- 元の表現の同じ比較射による、指定 fiber と元の Kan 値の実同値。 -/
def representationFiberValueEquivalence (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    QCatEquivalence (vertexFiber p b)
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (R.diagram.app (Opposite.op ⦋0⦌) b)).obj) :=
  (R.fiber_equivalence b).choose.trans (leftUnstraighteningFiberValueEquivalence R.diagram b)

/-- 元の表現比較の fiber と値への同じ比較は、元の指定辺の実輸送に全自然。 -/
def representationValueTransportIso (R : LeftTransportRepresentation p)
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    FunctorIso (edgeTransport p e ≫ (representationFiberValueEquivalence p R b).hom)
      ((representationFiberValueEquivalence p R a).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (e.map R.diagram))) := by
  have h := FunctorIso.postcomp
    (leftFibrationMap_transportIso p (leftUnstraighteningProjection R.diagram)
      R.comparison R.over_base e) (leftUnstraighteningFiberValueEquivalence R.diagram b).hom
  have k := FunctorIso.precomp (unstraighteningValueTransportIso R.diagram e)
    (vertexFiberMap p (leftUnstraighteningProjection R.diagram) R.comparison R.over_base a)
  simp only [Category.assoc] at h k
  simpa only [representationFiberValueEquivalence, QCatEquivalence.trans,
    IsQCatEquivalence.choose, Category.assoc] using h ≪≫ k

end SerrePositivity.InfinityCategories.F2.Compact
