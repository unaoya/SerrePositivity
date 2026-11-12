module

public import SerrePositivity.KST.Spectra.PointedHomTransposeComponents

/-!
概要：全パラメータの転置を、パラメータの元の点つき部分対象への制限に照合する。
方針：uncurry してテンソル交換の自然性を使う。
規約：単射性・Kan 性不要。使われ方：相対厳密化の指定境界の保持。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 内部 Hom のパラメータへの制限を転置すると、元の同じパラメータの前合成。 -/
lemma transpose_pre_inner {T A B V : PointedSimplicialSet.{u}}
    (f : T ⟶ (ihom A).obj V) (j : B ⟶ A) :
    transpose (f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V) = j ≫ transpose f := by
  apply uncurry_injective
  unfold transpose
  conv_lhs => rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, uncurry_pre_app]
  conv_rhs => rw [uncurry_natural_left, uncurry_curry]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right]
  simp only [Category.assoc]

end SerrePositivity.KST.Spectra.PointedMapping
