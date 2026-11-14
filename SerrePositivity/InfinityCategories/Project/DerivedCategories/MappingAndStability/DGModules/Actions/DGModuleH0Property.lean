module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleObjectPresentation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoTriangulated

/-! # 実三角的対象条件を K(D) に戻す

概要：通常の h の同型で閉じた三角的対象条件は、H⁰ 比較の逆像でも三角的。
方針：三対象の実 cofiber 表示で各位置の閉性を反映し、整数シフト閉性を導く。
規約：比較関手の三角関手性を仮定しない。使われ方：有限 cell と実安定閉包の相互比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (Q : ObjectProperty (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)))

/-- 通常の h の対象条件を H⁰ 比較の逆関手に沿って K(D) に戻す。 -/
def dgModuleH0Property : ObjectProperty (ModuleHomotopyCategory A D) :=
  Q.inverseImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).inverse

variable [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]

/-- 逆像は同型で閉じる。 -/
instance dgModuleH0Property_isClosedUnderIsomorphisms :
    (dgModuleH0Property A D Q).IsClosedUnderIsomorphisms where
  of_iso e h := Q.prop_of_iso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).inverse.mapIso e) h

/-- 逆像は零対象を含む。 -/
instance dgModuleH0Property_containsZero : (dgModuleH0Property A D Q).ContainsZero where
  exists_zero := ⟨(moduleToHomotopy A D).obj (moduleZero A D),
    (moduleToHomotopy A D).map_isZero (moduleZero_isZero A D), Q.prop_of_isZero
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).inverse.map_isZero
        ((moduleToHomotopy A D).map_isZero (moduleZero_isZero A D)))⟩

/-- 実 cofiber 表示は第一対象の閉性を反映する。 -/
instance dgModuleH0Property_isTriangulatedClosed₁ :
    (dgModuleH0Property A D Q).IsTriangulatedClosed₁ := .mk' (by
  intro T hT ha hb
  obtain ⟨t, ht, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_objectPresentation A D T hT
  exact Q.prop_of_iso e₁.symm
    (Q.ext_of_isTriangulatedClosed₁ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht)
      (Q.prop_of_iso e₂ ha) (Q.prop_of_iso e₃ hb)))

/-- 実 cofiber 表示は中間対象の閉性を反映する。 -/
instance dgModuleH0Property_isTriangulatedClosed₂ :
    (dgModuleH0Property A D Q).IsTriangulatedClosed₂ := .mk' (by
  intro T hT ha hb
  obtain ⟨t, ht, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_objectPresentation A D T hT
  exact Q.prop_of_iso e₂.symm
    (Q.ext_of_isTriangulatedClosed₂ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht)
      (Q.prop_of_iso e₁ ha) (Q.prop_of_iso e₃ hb)))

/-- 実 cofiber 表示は第三対象の閉性を反映する。 -/
instance dgModuleH0Property_isTriangulatedClosed₃ :
    (dgModuleH0Property A D Q).IsTriangulatedClosed₃ := .mk' (by
  intro T hT ha hb
  obtain ⟨t, ht, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_objectPresentation A D T hT
  exact Q.prop_of_iso e₃.symm
    (Q.ext_of_isTriangulatedClosed₃ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht)
      (Q.prop_of_iso e₁ ha) (Q.prop_of_iso e₂ hb)))

/-- 逆像は全整数シフトを含む三角的対象条件。 -/
instance dgModuleH0Property_isTriangulated : (dgModuleH0Property A D Q).IsTriangulated where
  isStableUnderShiftBy n := ⟨fun _ ha => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangulatedClosed_shift _ n ha⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
