module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitParameterCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeFlip

/-!
概要：選んだ普遍余錐族の変数交換の頂点を元の余極限関手へ照合する。
方針：変数交換の頂点評価の公式を同じ右頂点へ適用する。
規約：元のパラメータ付き図式を保持する。
使われ方：余極限単位の Hom 判定の両端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：選んだパラメータ余錐の頂点は元の余極限関手の合成の頂点。
方針：同じ余錐族の右頂点評価を交換する。
規約：頂点の再選択をしない。
使われ方：元の余極限関手からの Hom の普遍性。 -/
lemma chosenColimitParameterCocone_vertex {K A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) (U : A ⟶ (ihom K).obj X) :
    (chosenColimitParameterCocone hX U).vertex =
      functorVertex (U ≫ chosenColimitFunctor K X hX) := by
  change (internalHomFlipHomEquiv A (join K Δ[0]) X
    (U ≫ chosenColimitCoconeFamily K X hX)).app _ (coconeRightApexVertex K) = _
  rw [internalHomFlipHomEquiv_app_zero]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
