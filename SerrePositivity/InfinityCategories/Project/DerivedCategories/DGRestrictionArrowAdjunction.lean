module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionRepresentableArrows

/-! # 制限代表加群への閉射の導来随伴による正規化

概要：制限代表加群への閉射の主導来像は、正規化した代表延長同型による転置と一致する。
方針：代表上の単位の式と、導来随伴・制限計算の後合成の自然性を使う。
規約：同型の選択の正規化を式に保持。使われ方：roof 比較式の商側への反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 制限代表への射の主導来像と、実際の導来随伴の転置の一致。 -/
lemma dgRestrictionRepresentableArrow_homEquiv {x z : ClosedCategory A D}
    (k : F.onClosed.obj x ⟶ F.onClosed.obj z) :
    dgDerivedExtensionHomEquiv A D E F _ _
      ((derivedExtensionRepresentableUnitIso A D E F x).hom ≫
        (moduleToDerived A E).map ((dgYoneda A E).onClosed.map k)) =
      (moduleToDerived A D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow A D E F k) ≫
        (dgDerivedRestrictionComputation A D E F
          ((dgYoneda A E).onClosed.obj (F.onClosed.obj z))).inv := by
  rw [dgDerivedExtensionHomEquiv_naturality_right,
    derivedExtensionRepresentableUnitIso_homEquiv, Category.assoc,
    ← dgDerivedRestrictionComputation_inv_naturality, ← Category.assoc,
    ← (moduleToDerived A D).map_comp, dgModuleRestriction_map]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
