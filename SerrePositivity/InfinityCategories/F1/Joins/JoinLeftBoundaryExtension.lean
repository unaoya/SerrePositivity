module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinLeftBoundaryLifting
public import SerrePositivity.InfinityCategories.Core.PrecompositionRelativeLifting

/-!
概要：部分パラメータの join と左因子上の図式を同時に保つ関手の延長。
方針：相対境界の単射に沿う制限の持ち上げ性を、pushout の内部 Hom の引き戻しで記述する。
規約：延長するパラメータ射は単射かつ前合成の同値条件を満たす。
使われ方：Kerodon §4.6.6、部分族の逆の選択と固定始点を両立する相対延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：join 図式の族は部分パラメータと左因子上の指定を同時に保って延長できる。
方針：二つの指定を内部 Hom の引き戻しで相対境界へ貼り、前合成の持ち上げ性を使う。
規約：X のみ quasicategory、i と e は単射で e は普遍的な前合成の同値。
使われ方：Kerodon §4.6.6、右 pinched 模型の比較の厳密な左逆の構成。 -/
lemma exists_joinDiagramFamily_extension_of_leftBoundary
    {E F A B X : SSet.{u}} [Quasicategory X]
    (e : E ⟶ F) [Mono e] (he : IsPrecompositionEquivalence e)
    (i : A ⟶ B) [Mono i] (K : SSet.{u})
    (u : E ⟶ (ihom (join B K)).obj X)
    (v : F ⟶ (ihom (join A K)).obj X) (w : F ⟶ (ihom B).obj X)
    (hv : e ≫ v = u ≫ (pre (joinMap i (𝟙 K))).app X)
    (hw : e ≫ w = u ≫ (pre (joinInl B K)).app X)
    (hvw : v ≫ (pre (joinInl A K)).app X = w ≫ (pre i).app X) :
    ∃ U : F ⟶ (ihom (join B K)).obj X,
      e ≫ U = u ∧ U ≫ (pre (joinMap i (𝟙 K))).app X = v ∧
        U ≫ (pre (joinInl B K)).app X = w := by
  have := he.hasLiftingProperty_pre (joinLeftBoundaryMap i K) X
  exact exists_joinDiagramFamily_extension_of_leftBoundary_of_hasLiftingProperty
    e i K u v w hv hw hvw

end SerrePositivity.InfinityCategories
