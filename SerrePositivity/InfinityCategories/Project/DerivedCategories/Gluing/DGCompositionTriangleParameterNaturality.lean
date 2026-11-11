module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTriangleFamily
/-! # 同じ標準合成三角形の全入力自然性

概要：標準 coherent 合成三角形を、入力の制限を保って比較する。
方針：join のパラメーター自然性を slice の二単体へ移し、同じ coherent prism を使う。
規約：Small 仮定や三角形の再選択を導入しない。
使われ方：元 Hom 全体での native 標準面を、正本係数三角形へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet DifferentialGraded
open scoped _root_.Simplicial
lemma dgGluingJoinParameterComparison_parameter {A B K L : SSet.{u}} (i : L ⟶ K) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison A B K =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison A B L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (A ◁ i) (𝟙 B) := by
  have hn : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ◁ i) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) K).hom =
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) L).hom ≫ (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) := rfl
  have hb : (i ▷ A) ≫ (β_ K A).hom = (β_ L A).hom ≫ (A ◁ i) := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_naturality i A B), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hb, Category.id_comp]
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (β_ L A).hom (A ◁ i) (𝟙 B) (𝟙 B)
  simp only [Category.id_comp] at hj
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison, Category.assoc] using
    congrArg (fun k => (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) L).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft L A B ≫ k) hj
lemma dgGluingSlicePrismTriangle_parameter {K L X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}
    (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (i : L ⟶ K) :
    (Δ[2] ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle ((Δ[1] ◁ i) ≫ s) := by
  have hn : (Δ[2] ◁ i) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ▷ K) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ▷ L) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[1] Δ[0] ◁ i) := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle, ← Category.assoc, hn, Category.assoc,
    reassoc_of% (dgGluingJoinParameterComparison_parameter (A := Δ[1]) (B := Δ[0]) i),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]
  rfl
lemma dgGluingDGCompositionTriangleFamily_precomp (R : Type u) [CommRing R]
    (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    {K L : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z)
    (i : L ⟶ K) :
    (Δ[2] ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R D f g =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R D (i ≫ f) (i ≫ g) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily, dgGluingSlicePrismTriangle_parameter,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_precomp]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
