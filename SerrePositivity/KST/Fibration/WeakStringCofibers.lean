module
public import SerrePositivity.KST.Fibration.WeakStringEdges

/-! # 全有限 W 列の全辺に対する同じ cofiber 補完

元の相対 cofiber 射影の一つの厳密な切断を、全列・全合成辺に共通に使う。
補完とその核値 quotient は全再添字と厳密に可換する。
三辺の cofiber を結ぶ八面体の族と列全体の加法性は別工程である。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 既存の coherent な逆は、元の W 底辺を厳密に固定する切断でもある。 -/
lemma weakArrowCofiberEquivalence_inv_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakArrowCofiberEquivalence q).inv ≫ (weakArrowCofiberEquivalence q).hom =
      𝟙 (weakArrowModel q) := by
  apply Subtype.ext
  exact Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (weakCofiberProjection q))

/-- 全列・全合成辺に共通の、核に cofiber を持つ元の補完。 -/
def weakStringCofiberExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : weakStringModel q n ⟶ weakCofiberModel q :=
  weakStringEdgeExact q α ≫ (weakArrowCofiberEquivalence q).inv

/-- 補完した元の底辺は、抽出した実合成辺そのものである。 -/
lemma weakStringCofiberExact_projection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    weakStringCofiberExact q α ≫ (weakArrowCofiberEquivalence q).hom =
      weakStringEdgeExact q α := by
  rw [weakStringCofiberExact, Category.assoc, weakArrowCofiberEquivalence_inv_hom,
    Category.comp_id]

/-- 同じ補完の選択は、面・退化・合成辺の全ての制限と厳密に可換する。 -/
lemma weakStringCofiberExact_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    weakStringExactMap q θ ≫ weakStringCofiberExact q α =
      weakStringCofiberExact q (α ≫ θ) := by
  rw [weakStringCofiberExact, weakStringCofiberExact, ← Category.assoc,
    weakStringEdgeExact_reindex]

/-- 元の全合成辺の cofiber を、実際の核部分圏に値を持つ完全関手として保持する。 -/
def weakStringKernelCofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    weakStringModel q n ⟶ closedStableModel (kernelClosedPredicate q) :=
  weakStringCofiberExact q α ≫
    relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)

/-- 核値 cofiber も全再添字と厳密に可換する。 -/
lemma weakStringKernelCofiber_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    weakStringExactMap q θ ≫ weakStringKernelCofiber q α =
      weakStringKernelCofiber q (α ≫ θ) := by
  rw [weakStringKernelCofiber, weakStringKernelCofiber, ← Category.assoc,
    weakStringCofiberExact_reindex]

end SerrePositivity.KST.Fibration
