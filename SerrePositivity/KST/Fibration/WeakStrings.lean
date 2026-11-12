module
public import SerrePositivity.KST.Fibration.WeakArrowCategory

/-! # W 辺の全有限列

標準単体上の実図式のうち、商像の全辺が可逆となる図式を全部分圏として保持する。
隣接辺だけでなく全合成辺を含めるので、全ての面・退化による制限を厳密に定義できる。
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

/-- 標準単体上の関手頂点が表す、元の高次単体。 -/
def simplexVertexValue {B : SSet.{u}} (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj B) _⦋0⦌) : B.obj (Opposite.op n) :=
  SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B).symm v)

/-- 商に写した実図式の全辺が可逆である条件。 -/
def weakStringPredicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj B.obj) _⦋0⦌) : Prop :=
  q.hom.app (Opposite.op n) (simplexVertexValue n v) ∈
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).obj (Opposite.op n)

/-- W 辺の全有限列と、それらの間の全自然変換を持つ ∞ 圏。 -/
def weakStringCategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (stdSimplex.obj n)).obj B.obj) (weakStringPredicate q n)

instance weakStringCategory_quasicategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : Quasicategory (weakStringCategory q n) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n) : SSet.{u}))

/-- 関手頂点の全単体表示は、元の標準単体の再添字と厳密に可換。 -/
lemma simplexVertexValue_reindex {B : SSet.{u}} {m n : SimplexCategory} (θ : m ⟶ n)
    (v : ((ihom (stdSimplex.obj n)).obj B) _⦋0⦌) :
    simplexVertexValue m (((pre (stdSimplex.map θ)).app B).app (Opposite.op ⦋0⦌) v) =
      B.map θ.op (simplexVertexValue n v) := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B).surjective v
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj m) B).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj m) B) (stdSimplex.map θ ≫ F))) =
    B.map θ.op (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B) F)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact (SSet.yonedaEquiv_naturality θ F).symm

/-- 全合成辺を含む W 条件は、全ての面・退化による制限で保存される。 -/
lemma weakStringPredicate_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n)
    (v : ((ihom (stdSimplex.obj n)).obj B.obj) _⦋0⦌) (hv : weakStringPredicate q n v) :
    weakStringPredicate q m
      (((pre (stdSimplex.map θ)).app B.obj).app (Opposite.op ⦋0⦌) v) := by
  unfold weakStringPredicate
  rw [simplexVertexValue_reindex, NatTrans.naturality_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).map θ.op hv

/-- W 辺の列への、元の標準単体の制限。 -/
def weakStringMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) : weakStringCategory q n ⟶ weakStringCategory q m :=
  fullPredicateMap ((pre (stdSimplex.map θ)).app B.obj)
    (weakStringPredicate q n) (weakStringPredicate q m) (weakStringPredicate_reindex q θ)

/-- 列の制限を含めると、元の関手圏の前合成を回収する。 -/
lemma weakStringMap_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    weakStringMap q θ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q m)).ι =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
          (pre (stdSimplex.map θ)).app B.obj := rfl

end SerrePositivity.KST.Fibration
