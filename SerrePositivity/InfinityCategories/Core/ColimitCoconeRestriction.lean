module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：余錐を部分図式へ制限する。
方針：join の左因子で前合成する。
規約：頂点を表す右の零単体は変えない。
使われ方：貼り合わせの有限部分図式への余錐の制限。 -/
def JoinCocone.restrict {K₀ K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (f : K₀ ⟶ K) :
    JoinCocone (f ≫ p) :=
  ⟨joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ c.val, by
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, c.property]⟩


end SerrePositivity.InfinityCategories
