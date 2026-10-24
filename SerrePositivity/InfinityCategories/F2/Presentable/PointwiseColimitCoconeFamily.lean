module

public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorRelativeInitial
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryIso
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：各点で普遍な全余錐族は関手圏内でも普遍余錐である。
方針：各点の相対始点境界充填を内部 Hom に上げ、変数交換同型で移す。
規約：全余錐族の高次自然性を保持する。
使われ方：余極限関手の随伴と有限余積の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：各点で普遍な余錐族の変数交換は関手圏でも相対始点境界充填を持つ。
方針：点ごとの充填を内部 Hom でまとめ、交換同型の厳密な可換性で移送する。
規約：族のパラメータに quasicategory 性を要求しない。
使われ方：選んだ全余極限族の Hom 普遍性。 -/
lemma initialBoundaryLifting_flipped_coconeFamily
    {K A X : SSet.{u}} (s : A ⟶ (ihom (join K Δ[0])).obj X)
    (hs : ∀ a, InitialBoundaryLifting (coconeRestriction K X)
      (s.app (Opposite.op ⦋0⦌) a)) :
    InitialBoundaryLifting (coconeRestriction K ((ihom A).obj X))
      (functorVertex (internalHomFlipHomEquiv _ _ _ s)) := by
  have h := initialBoundaryLifting_ihom_of_pointwise (coconeRestriction K X) s hs
  have ht := h.map_iso (internalHomSwapIso A (join K Δ[0]) X)
    (internalHomSwapIso A K X) (internalHomSwapIso_pre (A := A) (joinInl K Δ[0])).symm
  rw [internalHomSwapIso_functorVertex] at ht
  exact ht

end SerrePositivity.InfinityCategories.F2.Presentable
