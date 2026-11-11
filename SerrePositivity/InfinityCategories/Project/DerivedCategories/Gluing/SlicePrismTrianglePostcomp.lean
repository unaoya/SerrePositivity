module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SlicePrismTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-! # slice prism の三角形表示と標的への後合成

概要：全 prism の slice 自然性を、同じ全三角形族の自然性へ送る。
方針：join 上の uncurry の後合成則と、固定標的の等式輸送を使う。
規約：三角形やパラメーターを選び直さない。
使われ方：D の coherent prism 自然性から六つの射影等式を実例化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingSlicePrismTriangle_postcomp {K X Y : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⟶ X} (V : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)
    (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle V ≫ q := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle, Category.assoc]

lemma dgGluingSlicePrismTriangle_transport {K X : SSet.{u}}
    {p p' : (Δ[0] : SSet.{u}) ⟶ X} (h : p = p')
    (V : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (V ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle V := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
