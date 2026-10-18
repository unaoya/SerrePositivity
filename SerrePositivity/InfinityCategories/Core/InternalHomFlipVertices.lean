module

public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction

/-!
概要：二変数の内部 Hom の交換と頂点での評価の一致。
方針：内部 Hom の交換同型の評価の公式を零次成分で使う。
規約：単体集合はすべて任意。
使われ方：Kerodon §7.1.8 の自然な錐の構成と点ごとの評価の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：内部 Hom の二変数を交換した射の頂点での値は元の図式を評価した関手頂点。
方針：交換同型と評価の可換性を関手の頂点に適用する。
規約：quasicategory 性は不要。
使われ方：Kerodon §7.1.8 の選んだ各点の錐と自然な錐の整合。 -/
lemma internalHomFlipHomEquiv_app_zero {A B X : SSet.{u}}
    (f : A ⟶ (ihom B).obj X) (b : B _⦋0⦌) :
    (internalHomFlipHomEquiv A B X f).app (Opposite.op ⦋0⦌) b =
      functorVertex (f ≫ evaluateFunctorAt b) := by
  let g := internalHomFlipHomEquiv A B X f
  have hs : (internalHomSwapIso B A X).hom.app (Opposite.op ⦋0⦌) (functorVertex g) =
      functorVertex f := by
    rw [internalHomSwapIso_functorVertex]
    dsimp [g, internalHomFlipHomEquiv]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_uncurry]
  have he := congrArg
    (fun q : (ihom B).obj ((ihom A).obj X) ⟶ (ihom A).obj X ↦
      q.app (Opposite.op ⦋0⦌) (functorVertex g)) (internalHomSwapIso_evaluate B A X b)
  change ((ihom A).map (evaluateFunctorAt (Y := X) b)).app (Opposite.op ⦋0⦌)
      ((internalHomSwapIso B A X).hom.app (Opposite.op ⦋0⦌) (functorVertex g)) =
    (evaluateFunctorAt b).app (Opposite.op ⦋0⦌) (functorVertex g) at he
  rw [hs, evaluateFunctorAt_functorVertex] at he
  exact he.symm

end SerrePositivity.InfinityCategories
