module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteSSetProductUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.HomotopyLimitsPresentableSiftedFiniteFiberProduct

/-!
概要：元の有限共通 fiber 積への普遍射と、元の全射影による一意性。
方針：元の反復積の普遍射を、同じ底射との可換性で引き戻しへ持ち上げる。
規約：元の底射と全成分を変更しない。
使われ方：有限 coherent 積の小さい全空間からの指定比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 同じ底射を被覆する元の有限族を、元の有限共通 fiber 積へ持ち上げる。 -/
def finiteCommonFiberProductLift (n : ℕ) {B A : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (f : (i : Fin (n + 1)) → A ⟶ E i) (b : A ⟶ B) (h : ∀ i, f i ≫ p i = b) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift n f) b (by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_hom_ext n (fun _ ↦ B)
    intro i
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap_projection, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal_projection,
      Category.comp_id, h])

/-- 元の普遍射の全成分は元の指定射そのもの。 -/
lemma finiteCommonFiberProductLift_projection (n : ℕ) {B A : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (f : (i : Fin (n + 1)) → A ⟶ E i) (b : A ⟶ B) (h : ∀ i, f i ≫ p i = b)
    (i : Fin (n + 1)) : finiteCommonFiberProductLift n p f b h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i = f i := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection, ← Category.assoc, finiteCommonFiberProductLift,
    pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection]

/-- 元の普遍射は指定した元の底射を厳密に被覆する。 -/
lemma finiteCommonFiberProductLift_base (n : ℕ) {B A : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (f : (i : Fin (n + 1)) → A ⟶ E i) (b : A ⟶ B) (h : ∀ i, f i ≫ p i = b) :
    finiteCommonFiberProductLift n p f b h ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n) = b :=
  pullback.lift_snd _ _ _

/-- 元の非空有限共通 fiber 積への射は、元の全成分だけで一意に決まる。 -/
lemma finiteCommonFiberProduct_hom_ext (n : ℕ) {B A : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p}
    (h : ∀ i, f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i) : f = g := by
  apply pullback.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_hom_ext n E
    intro i
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection, Category.assoc] using h i
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection_base n p 0, ← Category.assoc,
      ← Category.assoc, h 0]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
