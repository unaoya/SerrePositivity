module
public import SerrePositivity.KST.Fibration.TopPostcomposition
public import SerrePositivity.KST.Fibration.WeakStringPostcomposition
public import SerrePositivity.KST.Fibration.WeakStringVertices

/-! # 元の全頂点評価と包含側の完全関手による後合成の厳密な自然性 -/

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

/-- 元の全頂点部分圏に値を持つ評価は、元の周囲の頂点評価を完全関手として回収する。 -/
lemma weakStringVertexTopExact_inclusion {B C : StableCategory.{u}} (q : ExactMap B C)
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    weakStringVertexTopExact q n j ≫
      closedStableInclusion (ClosedStablePredicate.top (sInputModel B)) =
        weakStringVertexExact q n j := Subtype.ext (weakStringVertexTopMap_ι q n j)

/-- 元の全頂点評価は、元の完全関手による後合成を厳密に保つ。 -/
lemma weakStringVertexExact_postcomp {A B C : StableCategory.{u}}
    (f : ExactMap A B) (q : ExactMap B C) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    weakStringPostExact f q n ≫ weakStringVertexExact q n j =
      weakStringVertexExact (f ≫ q : A ⟶ C) n j ≫ sInputExactMap f := by
  apply Subtype.ext
  change weakStringPostMap f q n ≫
    ((fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) =
    ((fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) ≫ f.hom
  rw [← Category.assoc, weakStringPostMap_ι, Category.assoc, ihom_postcomp_evaluate,
    ← Category.assoc]

/-- 有限比較の元の初期成分の値域も、同じ全頂点部分圏の後合成と厳密に可換。 -/
lemma weakStringVertexTopExact_postcomp {A B C : StableCategory.{u}}
    (f : ExactMap A B) (q : ExactMap B C) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    weakStringPostExact f q n ≫ weakStringVertexTopExact q n j =
      weakStringVertexTopExact (f ≫ q : A ⟶ C) n j ≫ topPostExact f := by
  apply closedStableInclusion_cancel (ClosedStablePredicate.top (sInputModel B))
  rw [Category.assoc, weakStringVertexTopExact_inclusion, Category.assoc,
    topPostExact_inclusion, ← Category.assoc, weakStringVertexTopExact_inclusion]
  exact weakStringVertexExact_postcomp f q n j

end SerrePositivity.KST.Fibration
