module
public import SerrePositivity.InfinityCategories.F1.FiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.LeftFibrationPrismTransport
/-!
概要：底も変わる実 left fibration の正方形は、同じ辺の輸送を比較する。
方針：元の実輸送 prism を全空間の射で後合成し、標的の実輸送 prism と比較する。
規約：両 fiber の実同値から輸送の同値性を保存・反映する。
使われ方：実 Hom 図式から普遍 pointed-space 図式への辺作用の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 底も動かす同じ正方形は、実辺輸送と fiber 射を関手同型まで可換にする。 -/
def dgLeftFibrationSquareTransportIso {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso (edgeTransport p e ≫ transportSquareFiberMap p q f g h b)
      (transportSquareFiberMap p q f g h a ≫ edgeTransport q (e.map g)) := by
  let H := (edgeTransport_isTransport p e).choose
  have hs := (edgeTransport_isTransport p e).choose_spec.1
  have ht := (edgeTransport_isTransport p e).choose_spec.2.1
  have hp := (edgeTransport_isTransport p e).choose_spec.2.2.1
  apply leftFibrationPrism_transportIso q (e.map g)
    (transportSquareFiberMap p q f g h a)
    (edgeTransport p e ≫ transportSquareFiberMap p q f g h b) (H ≫ f)
  · rw [← Category.assoc, hs, transportSquareFiberMap_ι]
  · rw [← Category.assoc, ht, Category.assoc, Category.assoc, transportSquareFiberMap_ι]
  · rw [Category.assoc, h, ← Category.assoc, hp, Category.assoc,
      SSet.yonedaEquiv_symm_comp]
    rfl
/-- 両 fiber 射が同値なら、同じ正方形は実辺輸送の同値性を保存・反映する。 -/
lemma dgLeftFibrationSquareTransport_isQCatEquivalence_iff {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (ha : IsQCatEquivalence (transportSquareFiberMap p q f g h a))
    (hb : IsQCatEquivalence (transportSquareFiberMap p q f g h b)) :
    IsQCatEquivalence (edgeTransport p e) ↔ IsQCatEquivalence (edgeTransport q (e.map g)) := by
  have H := dgLeftFibrationSquareTransportIso p q f g h e
  constructor
  · intro he
    exact ha.cancel_left ((he.comp hb).ofFunctorIso H)
  · intro he
    exact hb.cancel_right ((ha.comp he).ofFunctorIso H.symm)
end SerrePositivity.InfinityCategories
