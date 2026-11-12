module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionArrowAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepresentableDerivedMaps

/-! # 制限代表加群への主導来比較式を H⁰ に反映する

概要：像の二閉射の制限代表への主導来像の一致は、像 dg 圏の H⁰ の一致と同値。
方針：正規化した導来随伴で等号を戻し、代表加群の射影性と Yoneda の忠実性で反映する。
規約：制限関手自体の充満忠実性は仮定しない。使われ方：roof の実合成二単体の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表加群の主導来像における一致は、元の二閉射の H⁰ での一致を反映する。 -/
lemma dgRepresentableDerivedMap_eq_iff {x y : ClosedCategory A D} (f g : x ⟶ y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D f = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D g ↔
      (toHomotopy A D).map f = (toHomotopy A D).map g := by
  let hP := representable_homotopicallyProjective A D x
  let : (dgYoneda A D).onHomotopy.Faithful :=
    (dgYoneda A D).onHomotopy_faithful_of_homIso (fun x y => by
      change IsIso (yonedaHom A D x y)
      unfold yonedaHom
      infer_instance)
  constructor
  · intro h
    apply (dgYoneda A D).onHomotopy.map_injective
    apply (moduleProjectiveDerivedHomEquiv A D hP _).injective
    change (moduleProjectiveDerivedHomEquiv A D hP _)
      ((moduleToHomotopy A D).map ((dgYoneda A D).onClosed.map f)) =
        (moduleProjectiveDerivedHomEquiv A D hP _)
          ((moduleToHomotopy A D).map ((dgYoneda A D).onClosed.map g))
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map]
    exact h
  · intro h
    have h' := congrArg (fun a => (dgYoneda A D).onHomotopy.map a) h
    change (moduleToHomotopy A D).map ((dgYoneda A D).onClosed.map f) =
      (moduleToHomotopy A D).map ((dgYoneda A D).onClosed.map g) at h'
    have he := congrArg (moduleProjectiveDerivedHomEquiv A D hP _) h'
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map] at he
    exact he

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 制限代表への主導来比較式は、像の二閉射の H⁰ の比較式そのもの。 -/
lemma dgRestrictionRepresentableArrow_derived_eq_iff {x z : ClosedCategory A D}
    (k l : F.onClosed.obj x ⟶ F.onClosed.obj z) :
    (moduleToDerived A D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow A D E F k) =
      (moduleToDerived A D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow A D E F l) ↔
      (toHomotopy A E).map k = (toHomotopy A E).map l := by
  constructor
  · intro h
    apply (dgRepresentableDerivedMap_eq_iff A E k l).mp
    apply (cancel_epi (derivedExtensionRepresentableUnitIso A D E F x).hom).mp
    apply (dgDerivedExtensionHomEquiv A D E F _ _).injective
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_homEquiv A D E F (x := x) (z := z) k).trans
      ((congrArg (fun a => a ≫ (dgDerivedRestrictionComputation A D E F
        ((dgYoneda A E).onClosed.obj (F.onClosed.obj z))).inv) h).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_homEquiv A D E F (x := x) (z := z) l).symm)
  · intro h
    have he := (dgRepresentableDerivedMap_eq_iff A E k l).mpr h
    have hc := congrArg (fun a => dgDerivedExtensionHomEquiv A D E F _ _
      ((derivedExtensionRepresentableUnitIso A D E F x).hom ≫ a)) he
    change dgDerivedExtensionHomEquiv A D E F _ _
      ((derivedExtensionRepresentableUnitIso A D E F x).hom ≫
        (moduleToDerived A E).map ((dgYoneda A E).onClosed.map k)) =
      dgDerivedExtensionHomEquiv A D E F _ _
        ((derivedExtensionRepresentableUnitIso A D E F x).hom ≫
          (moduleToDerived A E).map ((dgYoneda A E).onClosed.map l)) at hc
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_homEquiv A D E F (x := x) (z := z) k,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_homEquiv A D E F (x := x) (z := z) l] at hc
    exact (cancel_mono _).mp hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
