module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：任意の同じ矢印頂点を持つ区間 Hom の座標変更は二端評価と可換である。
方針：端点の等式輸送を一般形で相殺して元の二合成対応へ戻す。
規約：全区間と四頂点を保持する。使われ方：元 lax Hom 標的の座標輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
variable {Z : SSet.{u}} {a b c d : Z _⦋0⦌} (f : Z.Edge a b) (g : Z.Edge c d)
  {x y : ((ihom (Δ[1] : SSet.{u})).obj Z) _⦋0⦌}
  (hx : x = functorVertex (SSet.yonedaEquiv.symm f.edge))
  (hy : y = functorVertex (SSet.yonedaEquiv.symm g.edge))

def dgGluingArrowCoordinateIso :=
  intervalEndpointIso hx hy ≪≫ (dgGluingArrowCompositionIso f g).symm

def dgGluingArrowBaseCoordinateIso :=
  intervalEndpointIso
    ((congrArg ((F2.arrowEndpointPair Z).app (Opposite.op ⦋0⦌)) hx).trans
      (dgGluingArrowEndpointPair_vertex f))
    ((congrArg ((F2.arrowEndpointPair Z).app (Opposite.op ⦋0⦌)) hy).trans
      (dgGluingArrowEndpointPair_vertex g)) ≪≫
    (dgGluingIntervalMappingProductIso (X := Z) (Y := Z) a c b d).symm

lemma dgGluingArrowCoordinateIso_endpoints :
    (dgGluingArrowCoordinateIso f g hx hy).inv ≫
      intervalMappingPostOfEq (F2.arrowEndpointPair Z) x y rfl rfl ≫
        (dgGluingArrowBaseCoordinateIso f g hx hy).hom =
    dgGluingArrowCompositionEndpointPair f g := by
  rw [dgGluingArrowCoordinateIso, Iso.trans_inv, Iso.symm_inv,
    dgGluingArrowBaseCoordinateIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [reassoc_of% dgGluingIntervalPostOfEq_endpoint_naturality]
  exact dgGluingArrowCompositionIso_hom_endpoints f g

end SerrePositivity.InfinityCategories
