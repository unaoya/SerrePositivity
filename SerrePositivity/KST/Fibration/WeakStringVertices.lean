module
public import SerrePositivity.KST.Fibration.WeakStringsExact

/-! # 有限 W 列の元の頂点評価

全高次図式を保つ頂点評価を完全関手にし、全ての列の制限との可換性を証明する。
K-1 の既存の相対加法性の標的と照合するため、全頂点部分圏への同じ評価も保持する。
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

/-- 元の列の指定頂点への完全な評価。 -/
def weakStringVertexExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (j : Fin (n.len + 1)) : weakStringModel q n ⟶ sInputModel B :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j),
    (closedStableInclusion (weakStringClosedPredicate q n)).property.comp
      (evaluateFunctorAt_preservesSConstructionData (stdSimplex.obj₀Equiv.symm j)).toCofiberData⟩

/-- 頂点評価は元の全ての再添字と厳密に可換する。 -/
lemma weakStringVertexExact_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (j : Fin (m.len + 1)) :
    weakStringExactMap q θ ≫ weakStringVertexExact q m j =
      weakStringVertexExact q n (θ.toOrderHom j) := by
  apply Subtype.ext
  change weakStringMap q θ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q m)).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) = _
  rw [← Category.assoc, weakStringMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 同じ頂点評価を、全頂点を持つ閉じた部分圏に値を持つ射として保持する。 -/
def weakStringVertexTopMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    (weakStringModel q n).carrier ⟶ closedSubcategory (ClosedStablePredicate.top (sInputModel B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (weakStringVertexExact q n j).val (fun _ => trivial)

/-- 全頂点部分圏の包含は、元の評価を回収する。 -/
lemma weakStringVertexTopMap_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    weakStringVertexTopMap q n j ≫
      (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val =
        (weakStringVertexExact q n j).val := rfl

/-- K-1 の全頂点部分圏に値を持つ同じ完全な頂点評価。 -/
def weakStringVertexTopExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    weakStringModel q n ⟶ closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  ⟨weakStringVertexTopMap q n j, by
    apply preservesCofiberData_fullSubcomplex_of_comp
      (ClosedStablePredicate.top (sInputModel B)).predicate
    change PreservesCofiberData (weakStringVertexTopMap q n j ≫
      (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val)
    rw [weakStringVertexTopMap_ι]
    exact (weakStringVertexExact q n j).property⟩

/-- 全頂点部分圏に値を持つ評価も、元の全ての再添字と厳密に可換する。 -/
lemma weakStringVertexTopExact_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (j : Fin (m.len + 1)) :
    weakStringExactMap q θ ≫ weakStringVertexTopExact q m j =
      weakStringVertexTopExact q n (θ.toOrderHom j) := by
  apply Subtype.ext
  have : Mono (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (sInputModel B).carrier
      (ClosedStablePredicate.top (sInputModel B)).predicate).ι)
  apply (cancel_mono (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val).1
  change (weakStringMap q θ ≫ weakStringVertexTopMap q m j) ≫ _ =
    weakStringVertexTopMap q n (θ.toOrderHom j) ≫ _
  rw [Category.assoc, weakStringVertexTopMap_ι, weakStringVertexTopMap_ι]
  exact congrArg Subtype.val (weakStringVertexExact_reindex q θ j)

end SerrePositivity.KST.Fibration
