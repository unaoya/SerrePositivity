module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnderSectionInitialBase
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：積の添字の頂点 fiber は、元のパラメータを保つグラフへの引き戻しと同型。
方針：全空間の射とその第一射影から、引き戻しと頂点 fiber の両普遍性を使う。
規約：元の全空間への射を変えず、充填性も要求しない。
使われ方：元の under 評価の同値性を添字上の scaffold の fiber 比較に使う。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I) (i : I)

/-- 同じグラフへの引き戻しから、添字の同じ頂点 fiber への射。 -/
def productGraphFiberMap : pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ snd B (nerve I)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (pullback.fst _ _) (by
    rw [← Category.assoc, pullback.condition, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase, lift_snd, SSet.comp_const])

/-- 元の全空間への射は変わらない。 -/
lemma productGraphFiberMap_ι : productGraphFiberMap p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ =
    pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) := rfl

/-- 添字の同じ fiber から元のグラフへの引き戻しへの逆射。 -/
def productGraphFiberInverse :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ snd B (nerve I)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) ⟶
      pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ p ≫ fst B (nerve I)) (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase, lift_fst, Category.comp_id]
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase, lift_snd, SSet.comp_const]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _)

/-- グラフへの元の引き戻しと添字の元の fiber の同型。 -/
def productGraphFiberIso : pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ snd B (nerve I)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) where
  hom := productGraphFiberMap p i
  inv := productGraphFiberInverse p i
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, productGraphFiberInverse, pullback.lift_fst,
        productGraphFiberMap_ι, Category.id_comp]
    · simp only [productGraphFiberInverse, Category.assoc, pullback.lift_snd,
        Category.id_comp]
      rw [← Category.assoc (productGraphFiberMap p i), productGraphFiberMap_ι]
      rw [← Category.assoc, pullback.condition, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase, lift_fst, Category.comp_id]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    rw [Category.assoc, productGraphFiberMap_ι, productGraphFiberInverse,
      pullback.lift_fst, Category.id_comp]

/-- 同じ fiber 同型は元の全空間への射を厳密に保つ。 -/
lemma productGraphFiberIso_ι : (productGraphFiberIso p i).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ =
    pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) := productGraphFiberMap_ι p i

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
