module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientZeroRecovery
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityQuotientValueCoordinates

/-!
概要：元の恒等点を保つ値同値と、実全族の零単体値比較を元の座標で結ぶ。
方針：同じ fiber 値比較の終点輸送と、元の指定二辺の実比較を合成する。
規約：元の指定恒等点と二つの既存値比較を保持する。
使われ方：K-B-S の恒等 span の像と既存指定点の同じ fiber 内での比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：元の q(x) fiber から、同じ零単体の元の Kan 値への既存指定比較。
方針：元の終点等式で既存の零単体値比較を前合成する。
規約：元の全族回収で使う比較と同じ値比較。
使われ方：既存指定恒等点を保つ元の値同値との照合。 -/
def weakIdentityQuotientZeroValueComparison :=
  eqToHom (congrArg (vertexFiber
    (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x)).symm) ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFiberValueEquivalence h x (transportSimplexIndex (n := ⦋0⦌) x)).hom

/-- 概要：元の零単体値比較は、既存指定恒等点を保つ元の値同値と全関手同型。
方針：同じ fiber 値比較の終点輸送と指定値辺の合成ホモトピーを使う。
規約：既存指定点を補助点へ置換せず、全 fiber の値比較を照合する。
使われ方：実全族写像の恒等 span 像の同じ fiber 内での正規化。 -/
def weakIdentityQuotientZeroValueIso :
    FunctorIso (weakIdentityQuotientZeroValueComparison h x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).hom := by
  let Q := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x
  let b := q.hom.app (Opposite.op ⦋0⦌) x
  let b' := q.hom.app (Opposite.op ⦋0⦌)
    ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
      (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))
  have hb : b = b' := (congrArg (q.hom.app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x)).symm
  let K := fun z => spaceInfinityObject (Q.app (Opposite.op ⦋0⦌) (ULift.up z))
  have hnat (z : C.obj _⦋0⦌) (hz : b = z) :
      eqToHom (congrArg (vertexFiber (smallLeftUnstraighteningProjection Q)) hz) ≫
        (smallLeftUnstraighteningFiberValueEquivalence Q z).hom =
      (smallLeftUnstraighteningFiberValueEquivalence Q b).hom ≫
        (eqToHom (congrArg K hz) : K b ⟶ K z) := by
    subst z
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (smallLeftUnstraighteningFiberValueEquivalence Q b).hom =
      (smallLeftUnstraighteningFiberValueEquivalence Q b).hom ≫ 𝟙 (K b).obj
    exact (Category.comp_id _).symm
  have hn := hnat b' hb
  change eqToHom (congrArg (vertexFiber (smallLeftUnstraighteningProjection Q)) hb) ≫
      (smallLeftUnstraighteningFiberValueEquivalence Q b').hom =
    (smallLeftUnstraighteningFiberValueEquivalence Q b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientValueCoordinateMap h x at hn
  have e := FunctorIso.precomp
    (functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientValueCoordinateHomotopy h x))
    (smallLeftUnstraighteningFiberValueEquivalence Q b).hom
  change FunctorIso
    (eqToHom (congrArg (vertexFiber (smallLeftUnstraighteningProjection Q)) hb) ≫
      (smallLeftUnstraighteningFiberValueEquivalence Q b').hom ≫
        F2.spaceInfinityEdgeValue
          (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x)))
    ((smallLeftUnstraighteningFiberValueEquivalence Q b).hom ≫
      F2.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientValueEdge h x))
  rw [← Category.assoc, hn, Category.assoc]
  exact e.symm

end SerrePositivity.KST.Fibration
