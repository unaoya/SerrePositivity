module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeRestriction
public import SerrePositivity.InfinityCategories.Core.InitialEquivalence
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.ColimitAttachmentLifting

/-! # 余極限頂点の付加と余錐の普遍性

概要：余極限余錐を付け加える図式の pushout に沿う coslice 制限は trivial Kan fibration。
方針：全境界の充填と、始対象性の同値不変性を使う。
規約：充填性は任意の値域、普遍性の保存・反映は quasicategory の下で示す。
使われ方：S4 の左押し出しを使う五頂点／四頂点の比較。
-/
@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余極限余錐を付加する pushout の残りの図式への coslice 制限は trivial Kan fibration。
方針：各境界包含の持ち上げ性に付加の充填補題を適用する。
規約：値域に追加の仮定を置かない。使われ方：貼り合わせの制限の同値。 -/
lemma cosliceRestriction_trivialKanFibration_of_colimit_attachment
    {K C D X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c)
    (i : K ⟶ C) (j : join K Δ[0] ⟶ D) (k : C ⟶ D)
    (hp : IsPushout (joinInl K Δ[0]) i j k) (F : D ⟶ X) (hj : j ≫ F = c.val) :
    TrivialKanFibration (sliceUnderRestrict F k) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  exact cosliceRestriction_lift_of_colimit_attachment c hc i j k hp F hj (boundary n)

/-- 概要：余極限余錐を付加した図式の余錐は残りの図式への制限で余極限性を判定できる。
方針：coslice 制限の trivial Kan fibration による始対象性の保存と反映を使う。
規約：値域は quasicategory、余錐の頂点は不変。
使われ方：S4 の左押し出しに基づく外側比較。 -/
lemma isColimitCone_iff_restrict_of_colimit_attachment
    {K C D X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCocone p)
    (hc : IsColimitCone c) (i : K ⟶ C) (j : join K Δ[0] ⟶ D) (k : C ⟶ D)
    (hp : IsPushout (joinInl K Δ[0]) i j k) {F : D ⟶ X} (hj : j ≫ F = c.val)
    (d : JoinCocone F) : IsColimitCone d ↔ IsColimitCone (d.restrict k) := by
  have := cosliceRestriction_trivialKanFibration_of_colimit_attachment c hc i j k hp F hj
  exact (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict F k)).isInitialVertex_iff d

end SerrePositivity.InfinityCategories
