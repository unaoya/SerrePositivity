module
public import SerrePositivity.KST.Fibration.WeakStringConstants

/-! # 元の定数 W 列の全単体作用素との自然性と元の全頂点評価 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の定数 W 列は、全ての列方向の面・退化と厳密に可換。 -/
lemma weakStringConstantExact_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    weakStringConstantExact q n ≫ weakStringExactMap q θ = weakStringConstantExact q m := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q m)).ι).1
  change ((weakStringConstantExact q n).val ≫ weakStringMap q θ) ≫ _ = _
  rw [Category.assoc, weakStringMap_ι, ← Category.assoc, weakStringConstantExact_ι,
    weakStringConstantExact_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  exact whiskerRight_snd (stdSimplex.map θ) B.obj

/-- 定数 W 列の元の任意の頂点評価は、元の入力の恒等関手そのもの。 -/
lemma weakStringConstantExact_vertex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    weakStringConstantExact q n ≫ weakStringVertexExact q n j = 𝟙 (sInputModel B) := by
  apply Subtype.ext
  change (weakStringConstantExact q n).val ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) = _
  rw [← Category.assoc, weakStringConstantExact_ι]
  exact constantFunctor_evaluation (C := B.obj) (stdSimplex.obj₀Equiv.symm j)

/-- 元の定数 W 列を、元の安定入力からの単体的な定数図式の自然変換として保持する。 -/
def weakStringStableConstant {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (Functor.const SimplexCategoryᵒᵖ).obj (sInputModel B) ⟶ weakStringStableSimplicial q where
  app n := weakStringConstantExact q n.unop
  naturality {n m} θ := by
    change 𝟙 _ ≫ weakStringConstantExact q m.unop =
      weakStringConstantExact q n.unop ≫ weakStringExactMap q θ.unop
    rw [Category.id_comp, weakStringConstantExact_reindex]

end SerrePositivity.KST.Fibration
