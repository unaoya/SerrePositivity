module
public import SerrePositivity.InfinityCategories.Stable.CosliceRestriction
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-! # Right anodyne な部分図式による余極限性の判定

概要：right anodyne な単射で図式を制限しても、与えられた余錐の余極限性は変わらない。
方針：coslice の制限の trivial Kan fibration 性と、始対象性の同値不変性を使う。
規約：余錐の頂点はそのまま保つ。
使われ方：S4 の右の span と部分長方形の普遍性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余錐を部分図式へ制限する。
方針：join の左因子で前合成する。
規約：頂点を表す右の零単体は変えない。
使われ方：貼り合わせの有限部分図式への余錐の制限。 -/
def JoinCocone.restrict {K₀ K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (f : K₀ ⟶ K) :
    JoinCocone (f ≫ p) :=
  ⟨joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ c.val, by
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, c.property]⟩

/-- 概要：right anodyne な単射による余錐の制限は余極限性を保ち反映する。
方針：余錐の coslice の制限が同値であることから始対象性を移す。
規約：X は quasicategory、図式の形状に有限性や quasicategory 性を課さない。
使われ方：右の span と部分長方形の余極限の同定。 -/
lemma isColimitCone_iff_restrict_of_rightAnodyne {K₀ K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) (f : K₀ ⟶ K) [Mono f]
    (hf : rightAnodyneExtensions f) : IsColimitCone c ↔ IsColimitCone (c.restrict f) := by
  have := sliceUnderRestrict_trivialKanFibration p f hf
  exact (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict p f)).isInitialVertex_iff c

/-- 概要：right anodyne な単射によって余極限余錐を部分図式へ制限できる。
方針：余極限性の同値判定の順方向を使う。
規約：頂点を変えない。
使われ方：S4 の貼り合わせの普遍性の一方向。 -/
lemma IsColimitCone.restrict_of_rightAnodyne {K₀ K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c : JoinCocone p} (hc : IsColimitCone c) (f : K₀ ⟶ K) [Mono f]
    (hf : rightAnodyneExtensions f) : IsColimitCone (c.restrict f) :=
  (isColimitCone_iff_restrict_of_rightAnodyne c f hf).1 hc

end SerrePositivity.InfinityCategories
