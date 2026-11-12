module
public import SerrePositivity.KST.Fibration.WeakStringsExact
public import SerrePositivity.KST.Fibration.RelativeSFunctor
public import SerrePositivity.KST.LocalizingInvariants.StableFunctorMaps

/-! # 元の包含側の完全関手による全 W 列の後合成 -/

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

/-- 元の関手頂点の実単体表示は、元の完全関手による後合成を保つ。 -/
lemma simplexVertexValue_postcomp {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (n : SimplexCategory) (v : ((ihom (stdSimplex.obj n)).obj A.obj) _⦋0⦌) :
    simplexVertexValue n (((ihom (stdSimplex.obj n)).map f.hom).app (Opposite.op ⦋0⦌) v) =
      f.hom.app (Opposite.op n) (simplexVertexValue n v) := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) A.obj).surjective v
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ B.obj).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ B.obj (F ≫ f.hom))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- 元の後合成は、合成した商の W 条件を元の商の W 条件へ送る。 -/
lemma weakStringPredicate_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj A.obj) _⦋0⦌)
    (hv : weakStringPredicate (f ≫ q : A ⟶ C) n v) :
    weakStringPredicate q n
      (((ihom (stdSimplex.obj n)).map f.hom).app (Opposite.op ⦋0⦌) v) := by
  unfold weakStringPredicate
  rw [simplexVertexValue_postcomp]
  exact hv

/-- 元の全 W 列の図式圏の、元の完全関手による後合成。 -/
def weakStringPostMap {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : weakStringCategory (f ≫ q : A ⟶ C) n ⟶ weakStringCategory q n :=
  fullPredicateMap ((ihom (stdSimplex.obj n)).map f.hom)
    (weakStringPredicate (f ≫ q : A ⟶ C) n) (weakStringPredicate q n)
    (weakStringPredicate_postcomp f q n)

/-- 後合成の元の包含後は、全関手圏での後合成そのもの。 -/
@[reassoc]
lemma weakStringPostMap_ι {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) :
    weakStringPostMap f q n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫
        (ihom (stdSimplex.obj n)).map f.hom := rfl

/-- 同じ元の後合成は、W 列の安定な入力の完全関手である。 -/
def weakStringPostExact {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : weakStringModel (f ≫ q : A ⟶ C) n ⟶ weakStringModel q n :=
  ⟨weakStringPostMap f q n, by
    apply preservesCofiberData_fullSubcomplex_of_comp (weakStringPredicate q n)
    rw [weakStringPostMap_ι]
    exact (closedStableInclusion (weakStringClosedPredicate (f ≫ q : A ⟶ C) n)).property.comp
      (exactMap_preservesSData (exactFunctorMap (stdSimplex.obj n) f)).toCofiberData⟩

end SerrePositivity.KST.Fibration
