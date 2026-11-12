module
public import SerrePositivity.KST.Fibration.WeakStringsExact
public import SerrePositivity.KST.Fibration.WeakArrowEquivalence

/-! # W 列の全合成辺の完全な抽出

任意の実合成辺への制限を W 辺図式圏の完全関手として構成する。
抽出は列の全再添字と厳密に可換し、高次自然変換も保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- W 列の実合成辺への制限。 -/
def weakStringEdgeMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : weakStringCategory q n ⟶ weakArrowCategory q :=
  fullPredicateMap ((pre (stdSimplex.map α)).app B.obj)
    (weakStringPredicate q n) (weakArrowPredicate q)
    (fun v hv => (weakStringPredicate_one_iff q _).1
      (weakStringPredicate_reindex q α v hv))

/-- 抽出した W 辺の周囲への包含は、元の前合成を回収する。 -/
lemma weakStringEdgeMap_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    weakStringEdgeMap q α ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
        (pre (stdSimplex.map α)).app B.obj := rfl

/-- 合成辺への制限は、元の関手圏の完全な制限である。 -/
lemma weakStringEdgeMap_preservesCofiberData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : PreservesCofiberData (weakStringEdgeMap q α) := by
  apply preservesCofiberData_fullSubcomplex_of_comp (weakArrowPredicate q)
  rw [weakStringEdgeMap_ι]
  exact (closedStableInclusion (weakStringClosedPredicate q n)).property.comp
    (diagramRestrictionMap B α).property

/-- 同じ全合成辺への制限を K-1 の完全関手として保持する。 -/
def weakStringEdgeExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : weakStringModel q n ⟶ weakArrowModel q :=
  ⟨weakStringEdgeMap q α, weakStringEdgeMap_preservesCofiberData q α⟩

/-- 全合成辺への抽出は、面・退化を含む全ての列の制限と厳密に可換する。 -/
lemma weakStringEdgeMap_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    weakStringMap q θ ≫ weakStringEdgeMap q α = weakStringEdgeMap q (α ≫ θ) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι).1
  rw [Category.assoc, weakStringEdgeMap_ι, ← Category.assoc, weakStringMap_ι,
    Category.assoc, weakStringEdgeMap_ι, stdSimplex.map_comp, pre_map, NatTrans.comp_app]

/-- 完全関手としても元の合成辺を厳密に回収する。 -/
lemma weakStringEdgeExact_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    weakStringExactMap q θ ≫ weakStringEdgeExact q α = weakStringEdgeExact q (α ≫ θ) :=
  Subtype.ext (weakStringEdgeMap_reindex q θ α)

end SerrePositivity.KST.Fibration
