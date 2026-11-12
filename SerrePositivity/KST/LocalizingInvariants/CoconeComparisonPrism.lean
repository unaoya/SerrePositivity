module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeComparisonPrism

public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.KST.LocalizingInvariants.SpanFamilyTransposeNaturality

/-!
概要：全余錐比較の同じ一次単体を、両変数の制限を保持する同じ全 prism へ移す。
方針：元の内部 Hom 交換と uncurry の自然性で全写像を計算する。
規約：端点の代表・比較辺・区間を選び直さず、元の一次単体だけを使う。
使われ方：K 始端比較と指定 S 始端比較の両制限一致を相対 Homotopy 延長へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma spanComparisonPrism_pre_diagram {K L L' X : SSet.{u}} (j : L' ⟶ L)
    (s : ((ihom L).obj ((ihom K).obj X)) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism s ≫ (pre j).app X =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism (((pre j).app ((ihom K).obj X)).app (Opposite.op ⦋1⦌) s) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism]
  rw [← uncurry_natural_right, Category.assoc,
    ← spanInternalHomSwap_pre_first, ← SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.KST.LocalizingInvariants
