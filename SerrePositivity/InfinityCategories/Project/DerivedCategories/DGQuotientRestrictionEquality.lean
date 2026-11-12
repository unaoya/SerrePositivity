module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionArrowReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientActualRoofs

/-! # 商の H⁰ の等号と元の代表加群比較の等号

概要：元の二閉射の商での H⁰ の一致は、制限代表への比較後の主導来等号と同値。
方針：制限代表射の等号の反映と、元の閉射での比較写像の自然性を使う。
規約：局所 K-flat 性はこの比較には不要。使われ方：相対零化の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の H⁰ の等号は、元の二射を制限代表へ写した主導来等号で判定できる。 -/
lemma dgQuotientClosed_eq_iff_restriction (P : Set D) {x y : ClosedCategory A D}
    (f g : x ⟶ y) :
    (toHomotopy A (QuotientObject D P)).map ((inclusion A D P).onClosed.map f) =
      (toHomotopy A (QuotientObject D P)).map ((inclusion A D P).onClosed.map g) ↔
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D f ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D g ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_derived_eq_iff A D (QuotientObject D P)
    (inclusion A D P) (x := x) (z := y) ((inclusion A D P).onClosed.map f)
    ((inclusion A D P).onClosed.map g)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_map, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap] using h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
