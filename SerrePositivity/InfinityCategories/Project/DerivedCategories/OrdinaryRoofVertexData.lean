module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofReverseVertexEdge
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OverIso

/-! # 通常の屋根の反対頂点と構造辺

概要：Over の反対 Under 表示の零単体と、Under の構造辺を元の指定射で評価する。
方針：零次の射列の外延性と、点の join の両逆性を使う。
規約：対象や射を選び直さない。使われ方：over 比較の頂点における辺の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial
variable {C : Type u} [Category.{u} C]

/-- Over の零単体を反対 Under の指定零単体へ送る。 -/
lemma ordinaryRoofOppositeVertex (c : C) (s : Over c) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverOppositeUnderIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((Under.opEquivOpOver c).inverse.obj (op s))) := by
  apply SSet.opObjEquiv.injective
  exact ComposableArrows.ext₀ rfl

/-- Under の指定零単体の辺は、その指定構造射。 -/
lemma ordinaryUnderVertexEdge (c : C) (s : Under c) :
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderSimplex c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)).val) = ComposableArrows.mk₁ s.hom := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)))) = _
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso.{u} 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0 := by
    apply Iso.ext
    rfl
  rw [hi, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  refine ComposableArrows.ext₁ (F := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s))
    (G := ComposableArrows.mk₁ s.hom) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
