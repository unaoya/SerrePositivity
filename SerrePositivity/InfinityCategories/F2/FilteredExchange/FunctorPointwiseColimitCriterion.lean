module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.F1B.FunctorRelativeInitial
public import SerrePositivity.InfinityCategories.F1B.KanInitialBoundaryIso
public import SerrePositivity.InfinityCategories.Stable.ColimitRelativeBoundary

/-!
概要：元の coherent 余錐が点ごとに余極限なら、関手単体集合でも余極限である。
方針：各点の相対始点境界充填を二重内部 Hom の交換で元の余錐へ移す。
規約：元の余錐全体を保持。使われ方：単体形状の filtered 極限交換と比較辺の可逆性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 点ごとの余極限性は、元の関手単体集合の余錐の相対始点境界充填を与える。 -/
lemma initialBoundaryLifting_coconeRestriction_of_pointwise {J K X : SSet.{u}}
    [Quasicategory X] {p : J ⟶ (ihom K).obj X} (c : JoinCocone p)
    (hc : IsPointwiseColimitCone c) :
    InitialBoundaryLifting (coconeRestriction J ((ihom K).obj X)) (functorVertex c.val) := by
  let T := join J (Δ[0] : SSet.{u})
  let f : K ⟶ (ihom T).obj X := curry ((β_ T K).hom ≫ uncurry c.val)
  have hs : (internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (functorVertex f) =
      functorVertex c.val := by
    rw [internalHomSwapIso_functorVertex]
    dsimp only [f]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_uncurry]
  have hf : ∀ k : K _⦋0⦌, f.app (Opposite.op ⦋0⦌) k =
      functorVertex (evaluateFunctorCocone c k).val := by
    intro k
    have he := congrArg
      (fun q : (ihom K).obj ((ihom T).obj X) ⟶ (ihom T).obj X =>
        q.app (Opposite.op ⦋0⦌) (functorVertex f)) (internalHomSwapIso_evaluate K T X k)
    change ((ihom T).map (evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
        ((internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (functorVertex f)) =
      (evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (functorVertex f) at he
    rw [hs, evaluateFunctorAt_functorVertex] at he
    exact he.symm
  have ht : InitialBoundaryLifting ((ihom K).map (coconeRestriction J X)) (functorVertex f) :=
    initialBoundaryLifting_ihom_of_pointwise (coconeRestriction J X) f (by
      intro k
      rw [hf]
      exact (hc k).initialBoundaryLifting)
  have hq : (internalHomSwapIso K T X).hom ≫ coconeRestriction J ((ihom K).obj X) =
      (ihom K).map (coconeRestriction J X) ≫ (internalHomSwapIso K J X).hom :=
    (internalHomSwapIso_pre (A := K) (X := X) (joinInl J Δ[0])).symm
  have h := ht.map_iso (internalHomSwapIso K T X) (internalHomSwapIso K J X) hq
  rwa [hs] at h

/-- 元の点ごとの余極限余錐は関手 ∞ 圏でも余極限余錐。 -/
lemma isColimitCone_of_pointwise {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p) (hc : IsPointwiseColimitCone c) :
    IsColimitCone c :=
  isColimitCone_of_initialBoundaryLifting_coconeRestriction c
    (initialBoundaryLifting_coconeRestriction_of_pointwise c hc)

end SerrePositivity.InfinityCategories.F2
