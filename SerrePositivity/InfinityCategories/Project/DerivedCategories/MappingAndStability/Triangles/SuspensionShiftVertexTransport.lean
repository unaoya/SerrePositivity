module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableHomotopyShiftComparison

/-! # D3 の suspension 比較と定値頂点への表示変更

概要：任意の h の対象から定値頂点への等号に沿って suspension 比較の成分を移す。
方針：対象の等式を消去し、頂点上の既知成分と Q の対象比較を合成する。
規約：安定構造の suspension 比較を使う。使われ方：D7 の mapTriangle の第三可換式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 定値頂点へ移した suspension 比較は複体シフトとの対象比較になる。 -/
lemma derivedSuspensionShiftIso_transport_vertex (x : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (hx : x = SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIso S).hom.app x ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map (eqToHom hx))⟦(1 : ℤ)⟧' ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X).hom⟦(1 : ℤ)⟧' =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map (eqToHom hx)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom := by
  cases hx
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIsoApp S (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X).hom⟦(1 : ℤ)⟧' = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIsoApp_vertex]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftObjectIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- 標準 suspension からの逆比較を合成すると、標準 cone 頂点からの比較だけが残る。 -/
lemma derivedSuspensionObjectIso_cancel_inv (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso.inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
      DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso_hom]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso, Iso.trans_hom, eqToIso.hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
