module
public import SerrePositivity.KST.Fibration.WeakStrings

/-! # W 辺の列の全単体的構造

元の標準単体の前合成を保持して、有限 W 列の面・退化を単体的対象に束ねる。
一辺の場合は既存の W 辺図式圏そのものと一致する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- W 列の恒等再添字は元の恒等射を保つ。 -/
lemma weakStringMap_id {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : SimplexCategory) :
    weakStringMap q (𝟙 n) = 𝟙 (weakStringCategory q n) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι).1
  dsimp only [weakStringCategory]
  rw [weakStringMap_ι, CategoryTheory.Functor.map_id, pre_id, NatTrans.id_app]
  simp only [Category.comp_id, Category.id_comp]

/-- W 列の再添字は元の合成を厳密に保つ。 -/
lemma weakStringMap_comp {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {l m n : SimplexCategory} (θ : l ⟶ m) (φ : m ⟶ n) :
    weakStringMap q (θ ≫ φ) = weakStringMap q φ ≫ weakStringMap q θ := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q l)).ι).1
  rw [weakStringMap_ι, Category.assoc, weakStringMap_ι, ← Category.assoc, weakStringMap_ι]
  rw [stdSimplex.map_comp, pre_map, NatTrans.comp_app, Category.assoc]

/-- 全有限 W 列の、全高次自然変換を保持した単体的 ∞ 圏の underlying 図式。 -/
def weakStringSimplicialCategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    SimplicialObject SSet.{u} where
  obj n := weakStringCategory q n.unop
  map θ := weakStringMap q θ.unop
  map_id n := weakStringMap_id q n.unop
  map_comp θ φ := weakStringMap_comp q φ.unop θ.unop

/-- 零段の W 条件は全ての対象に成立する。 -/
lemma weakStringPredicate_zero {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Δ[0] : SSet.{u})).obj B.obj) _⦋0⦌) : weakStringPredicate q ⦋0⦌ v :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _

/-- 一辺の列の条件は、元の W 辺図式の条件と同じである。 -/
lemma weakStringPredicate_one_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) :
    weakStringPredicate q ⦋1⦌ v ↔ weakArrowPredicate q v := by
  change q.hom.app _ (arrowVertexSimplex v) ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).obj _ ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (arrowVertexSimplex v)).map ((truncation 2).map q.hom))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (q.hom.app _ (arrowVertexSimplex v))) rfl).symm

/-- 一辺の段は、選択や同値な別模型を導入せず既存の W 辺図式圏と一致する。 -/
lemma weakStringCategory_one {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringCategory q ⦋1⦌ = weakArrowCategory q := by
  have hp : weakStringPredicate q ⦋1⦌ = weakArrowPredicate q :=
    funext (fun v => propext (weakStringPredicate_one_iff q v))
  exact congrArg (fun P => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom (Δ[1] : SSet.{u})).obj B.obj) P : SSet.{u})) hp

/-- 列の条件は、全ての実合成辺の W 所属で正確に判定できる。 -/
lemma weakStringPredicate_iff_allEdges
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj B.obj) _⦋0⦌) :
    weakStringPredicate q n v ↔
      ∀ α : ⦋1⦌ ⟶ n, B.obj.map α.op (simplexVertexValue n v) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  change (∀ α : ⦋1⦌ ⟶ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (C.obj.map α.op (q.hom.app _ (simplexVertexValue n v))))) ↔ _
  apply forall_congr'
  intro α
  rw [← NatTrans.naturality_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (B.obj.map α.op (simplexVertexValue n v))).map
      ((truncation 2).map q.hom))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (q.hom.app _ (B.obj.map α.op (simplexVertexValue n v)))) rfl).symm.trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h _).symm

end SerrePositivity.KST.Fibration
