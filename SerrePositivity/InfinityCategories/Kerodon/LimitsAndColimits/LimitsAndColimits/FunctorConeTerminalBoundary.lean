module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap

/-!
概要：点ごとの錐の相対終点境界充填を関手圏の錐へ移す。
方針：二重内部 Hom を交換し、点ごとの相対充填の移送定理を使う。
規約：点ごとの極限からの相対充填への方向は別に証明する。
使われ方：HTT 5.1.2.2、Kerodon Proposition 7.1.8.10（Tag 02XK） の絶対極限の準備。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：評価した錐の相対終点境界充填は関手圏の錐の相対終点境界充填を与える。
方針：内部 Hom の二つの始域を交換し、点ごとの充填を移送する。
規約：点ごとの仮定は極限性より強い相対充填として明記する。
使われ方：Kerodon Proposition 7.1.8.10（Tag 02XK） の空図式への還元。 -/
lemma terminalBoundaryLifting_coneRestriction_of_pointwise {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (hc : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c k).val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J ((ihom K).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J
  let f : K ⟶ (ihom T).obj X := curry ((β_ T K).hom ≫ uncurry c.val)
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex]
    dsimp [f]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_uncurry]
  have hf : ∀ k : K _⦋0⦌, f.app (Opposite.op ⦋0⦌) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c k).val := by
    intro k
    have he := congrArg
      (fun q : (ihom K).obj ((ihom T).obj X) ⟶ (ihom T).obj X ↦
        q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate K T X k)
    change ((ihom T).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) at he
    rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at he
    exact he.symm
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_ihom_of_pointwise (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X) f (by
      intro k
      rw [hf]
      exact hc k)
  have hq : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J ((ihom K).obj X) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K J X).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre (A := K) (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J)).symm
  have h := ht.map_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K J X) hq
  rwa [hs] at h

/-- 概要：評価した錐が錐の制限に対する相対終点境界充填を満たせば関手圏の極限錐となる。
方針：点ごとの相対充填を関手圏へ移し、fiber の終対象性で判定する。
規約：X は quasicategory。点ごとの極限性だけからの結論はまだ含めない。
使われ方：HTT 5.1.2.2 の相対境界判定から極限への接続。 -/
lemma isLimitCone_of_pointwise_terminalBoundaryLifting {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (hc : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c k).val)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_terminalBoundaryLifting_coneRestriction c
    (terminalBoundaryLifting_coneRestriction_of_pointwise c hc)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
