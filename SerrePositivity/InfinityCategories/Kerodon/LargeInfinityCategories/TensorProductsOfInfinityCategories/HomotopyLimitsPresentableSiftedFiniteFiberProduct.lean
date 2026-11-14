module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.HomotopyLimitsPresentableSiftedFiniteDiagonal

/-!
分割で生成：docstring を書き直すこと
概要：sifted な底上の元の有限非空 fiber 積の全空間 Kan 比較。
方針：元の全積射で元の有限対角を引き戻し、元の各射影の Kan 像を比較する。
規約：底の quasicategory 性は不要。元の全空間・射影・単位を保持する。
使われ方：P_Σ の sifted 余極限閉性に向けた、全有限積の元の全空間比較。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 元の有限非空族の全積射で元の対角を引き戻した、共通底の fiber 積。 -/
def finiteCommonFiberProduct (n : ℕ) {B : SSet.{u}} {E : Fin (n + 1) → SSet.{u}}
    (p : (i : Fin (n + 1)) → E i ⟶ B) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n)

/-- 元の共通 fiber 積から元の i 番目の全空間への射影。 -/
def finiteCommonFiberProductProjection (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (i : Fin (n + 1)) : finiteCommonFiberProduct n p ⟶ E i :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n E i

/-- 元の全射影は同じ元の底射影を被覆する。 -/
lemma finiteCommonFiberProductProjection_base (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (i : Fin (n + 1)) : finiteCommonFiberProductProjection n p i ≫ p i =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n) := by
  rw [finiteCommonFiberProductProjection, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap_projection, ← Category.assoc, pullback.condition,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal_projection, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
