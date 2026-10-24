module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitFunctor
public import SerrePositivity.InfinityCategories.F2.Presentable.PointwiseColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices

/-!
概要：選んだ余極限族を任意のパラメータの関手圏内の全余極限として保持する。
方針：全普遍余錐族を変数交換し、点ごとの始点境界充填をまとめる。
規約：元のパラメータ付き図式と余極限関手の合成を保つ。
使われ方：余極限関手の全 Hom 普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {K A X : SSet.{u}} [Quasicategory X]
  (hX : ∀ p : K ⟶ X, HasColimit p) (U : A ⟶ (ihom K).obj X)

/-- 概要：選んだ全余錐族の変数交換は元の図式族の全余錐。
方針：左端制限と変数交換の可換性を切断条件へ適用する。
規約：元の図式族を厳密に保持する。
使われ方：全パラメータの余極限性。 -/
def chosenColimitParameterCocone :
    JoinCocone (internalHomFlipHomEquiv _ _ _ U) where
  val := internalHomFlipHomEquiv _ _ _ (U ≫ chosenColimitCoconeFamily K X hX)
  property := by
    rw [← internalHomFlipHomEquiv_pre_app, Category.assoc]
    change internalHomFlipHomEquiv A K X
      (U ≫ chosenColimitCoconeFamily K X hX ≫ coconeRestriction K X) = _
    rw [chosenColimitCoconeFamily_restrict, Category.comp_id]

/-- 概要：選んだ図式族の全余錐は関手圏内の余極限である。
方針：同じ普遍余錐全部分複体の各頂点の条件を変数交換でまとめる。
規約：パラメータに quasicategory 性は不要。
使われ方：余極限関手の随伴の全 Hom 判定。 -/
lemma chosenColimitParameterCocone_isColimit :
    IsColimitCone (chosenColimitParameterCocone hX U) := by
  apply (isColimitCone_iff_initialBoundaryLifting _).mpr
  apply initialBoundaryLifting_flipped_coconeFamily
  intro a
  exact fullSubcomplexOnVertices_vertex
    ((chosenColimitSection K X hX).app (Opposite.op ⦋0⦌)
      (U.app (Opposite.op ⦋0⦌) a))

end SerrePositivity.InfinityCategories.F2.Presentable
