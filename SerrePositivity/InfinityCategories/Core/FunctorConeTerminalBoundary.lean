module

public import SerrePositivity.InfinityCategories.Core.ConeTerminalBoundary
public import SerrePositivity.InfinityCategories.Core.TerminalBoundaryIso
public import SerrePositivity.InfinityCategories.Core.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap

/-!
概要：点ごとの錐の相対終点境界充填を関手圏の錐へ移す。
方針：二重内部 Hom を交換し、点ごとの相対充填の移送定理を使う。
規約：点ごとの極限からの相対充填への方向は別に証明する。
使われ方：HTT 5.1.2.2、Kerodon Proposition 7.1.8.10 の絶対極限の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：評価した錐の相対終点境界充填は関手圏の錐の相対終点境界充填を与える。
方針：内部 Hom の二つの始域を交換し、点ごとの充填を移送する。
規約：点ごとの仮定は極限性より強い相対充填として明記する。
使われ方：Kerodon Proposition 7.1.8.10 の空図式への還元。 -/
lemma terminalBoundaryLifting_coneRestriction_of_pointwise {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : JoinCone p)
    (hc : ∀ k : K _⦋0⦌, TerminalBoundaryLifting (coneRestriction J X)
      (functorVertex (evaluateFunctorCone c k).val)) :
    TerminalBoundaryLifting (coneRestriction J ((ihom K).obj X)) (functorVertex c.val) := by
  let T := join (Δ[0] : SSet.{u}) J
  let f : K ⟶ (ihom T).obj X := curry ((β_ T K).hom ≫ uncurry c.val)
  have hs : (internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (functorVertex f) =
      functorVertex c.val := by
    rw [internalHomSwapIso_functorVertex]
    dsimp [f]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_uncurry]
  have hf : ∀ k : K _⦋0⦌, f.app (Opposite.op ⦋0⦌) k =
      functorVertex (evaluateFunctorCone c k).val := by
    intro k
    have he := congrArg
      (fun q : (ihom K).obj ((ihom T).obj X) ⟶ (ihom T).obj X ↦
        q.app (Opposite.op ⦋0⦌) (functorVertex f)) (internalHomSwapIso_evaluate K T X k)
    change ((ihom T).map (evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
        ((internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (functorVertex f)) =
      (evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (functorVertex f) at he
    rw [hs, evaluateFunctorAt_functorVertex] at he
    exact he.symm
  have ht : TerminalBoundaryLifting ((ihom K).map (coneRestriction J X)) (functorVertex f) :=
    terminalBoundaryLifting_ihom_of_pointwise (coneRestriction J X) f (by
      intro k
      rw [hf]
      exact hc k)
  have hq : (internalHomSwapIso K T X).hom ≫ coneRestriction J ((ihom K).obj X) =
      (ihom K).map (coneRestriction J X) ≫ (internalHomSwapIso K J X).hom :=
    (internalHomSwapIso_pre (A := K) (X := X) (joinInr Δ[0] J)).symm
  have h := ht.map_iso (internalHomSwapIso K T X) (internalHomSwapIso K J X) hq
  rwa [hs] at h

/-- 概要：評価した錐が錐の制限に対する相対終点境界充填を満たせば関手圏の極限錐となる。
方針：点ごとの相対充填を関手圏へ移し、fiber の終対象性で判定する。
規約：X は quasicategory。点ごとの極限性だけからの結論はまだ含めない。
使われ方：HTT 5.1.2.2 の相対境界判定から極限への接続。 -/
lemma isLimitCone_of_pointwise_terminalBoundaryLifting {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : JoinCone p)
    (hc : ∀ k : K _⦋0⦌, TerminalBoundaryLifting (coneRestriction J X)
      (functorVertex (evaluateFunctorCone c k).val)) : IsLimitCone c :=
  isLimitCone_of_terminalBoundaryLifting_coneRestriction c
    (terminalBoundaryLifting_coneRestriction_of_pointwise c hc)

end SerrePositivity.InfinityCategories
