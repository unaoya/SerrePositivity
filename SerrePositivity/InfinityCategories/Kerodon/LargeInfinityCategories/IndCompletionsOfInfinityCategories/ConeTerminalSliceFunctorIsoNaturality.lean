module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeTerminalSliceComparisonNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeFunctorVertexIsoNaturality

/-!
概要：同じ終点への全余錐の相対比較は、元の試験形状の制限でも同じ指定比較を回収する。
方針：right-anodyne 相対比較の自然性と、標準持ち上げの厳密な全自然性を合成する。
規約：元の底と終点を固定し、同型の存在だけでなく指定値そのものを保持する。
使われ方：指定された極大点評価下の変換を、同じ旧族で保持する相対余錐の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {A A₀ X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
  (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
  (W : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x))
  (hp : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x) = b)
  (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x))
  (k : A₀ ⟶ A)
/-- 概要：元の全底余錐と恒等終点を固定した比較を、元の全 slice 族の同型で読む。
方針：元の相対関手空間の包含。規約：指定同型を保持。使われ方：旧族の比較の帰還。 -/
def coneTerminalSliceFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso W (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTerminalSliceLift x b hb) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeFunctorVertexIsoImage _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTerminalSliceRelativeIso x b hb W hp ht)
/-- 概要：同じ全 slice 族の指定比較は、旧族で元の同じ比較へ制限される。
方針：相対比較と元の包含の自然性。規約：同じ指定値。使われ方：元の指定変換の保持。 -/
lemma coneTerminalSliceFunctorIso_precomp : HEq
    ((coneTerminalSliceFunctorIso x b hb W hp ht).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap k (𝟙 Δ[0])))
    (coneTerminalSliceFunctorIso x (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]; exact hb)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp])
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]; exact ht)) := by
  dsimp only [coneTerminalSliceFunctorIso]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeFunctorVertexIsoImage_precomp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeFunctorVertexIsoImage_heq
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTerminalSliceLift_precomp x b hb k
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTerminalSliceRelativeIso_precomp x b hb W hp ht k
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
