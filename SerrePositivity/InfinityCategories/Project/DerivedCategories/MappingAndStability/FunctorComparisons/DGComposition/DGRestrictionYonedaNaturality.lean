module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGExtensionRepresentableClosed
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Equivalence

/-! # 代表加群の制限比較の元の閉射に対する自然性

概要：元の閉 dg 射を先に Yoneda で写しても、制限比較の後で像の Yoneda を適用しても一致。
方針：延長–制限の単位の自然性と、代表加群延長同型の閉射の自然性を合成する。
規約：全 Hom の平坦性は不要。使われ方：roof 比較式を導来随伴に移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 代表加群から制限代表加群への比較は、元の閉射について自然。 -/
lemma dgRepresentableRestrictionMap_naturality {x y : ClosedCategory A D} (f : x ⟶ y) :
    (dgYoneda A D).onClosed.map f ≫ representableRestrictionMap A D E F y =
      representableRestrictionMap A D E F x ≫ (moduleRestriction A D E F.op).map
        ((dgYoneda A E).onClosed.map (F.onClosed.map f)) := by
  let R := (dgModuleRestriction A D E F.op).onClosed
  let L := (dgModuleExtension A D E F).onClosed
  let adj := dgModuleEnrichedRestrictionAdjunction A D E F
  let a := (dgYoneda A D).onClosed.map f
  let b := (dgYoneda A E).onClosed.map (F.onClosed.map f)
  have hx : adj.unit.app ((dgYoneda A D).onClosed.obj x) ≫
      R.map (dgModuleExtensionRepresentableIso A D E F x).hom =
        representableRestrictionMap A D E F x := by
    rw [dgModuleEnrichedRestrictionAdjunction_unit, dgModuleRestriction_map]
    exact functorExtensionUnit_representable A D E F x
  have hy : adj.unit.app ((dgYoneda A D).onClosed.obj y) ≫
      R.map (dgModuleExtensionRepresentableIso A D E F y).hom =
        representableRestrictionMap A D E F y := by
    rw [dgModuleEnrichedRestrictionAdjunction_unit, dgModuleRestriction_map]
    exact functorExtensionUnit_representable A D E F y
  have hn : a ≫ adj.unit.app ((dgYoneda A D).onClosed.obj y) =
      adj.unit.app ((dgYoneda A D).onClosed.obj x) ≫ R.map (L.map a) := adj.unit.naturality a
  rw [← hx, ← hy, ← dgModuleRestriction_map]
  change a ≫ (_ ≫ R.map _) = (_ ≫ R.map _) ≫ R.map b
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgExtensionRepresentableIso_closed_naturality, R.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
