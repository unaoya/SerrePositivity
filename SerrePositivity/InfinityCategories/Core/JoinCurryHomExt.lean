module

public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-!
概要：join からの射を標準単体の一方の因子と固定因子で比較する外延性。
方針：slice または coslice の curry の各単体で比較する。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon §4.6.2 の fat join 比較のエピ性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：join からの射は固定した右因子と左因子の全標準単体で比較できる。
方針：slice の curry の単体の等式から元の射の等式へ戻る。
規約：両因子と標的は任意。
使われ方：Kerodon §4.6.2 の二変数の比較。 -/
lemma join_left_hom_ext {A K X : SSet.{u}} {f g : join A K ⟶ X}
    (hK : joinInr A K ≫ f = joinInr A K ≫ g)
    (hA : ∀ n (a : (Δ[n] : SSet.{u}) ⟶ A), joinMap a (𝟙 K) ≫ f = joinMap a (𝟙 K) ≫ g) :
    f = g := by
  have h : sliceOverCurry f rfl = sliceOverCurry g hK.symm := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    exact hA n (SSet.yonedaEquiv.symm a)
  simpa only [sliceOverUncurry_curry] using congrArg sliceOverUncurry h

/-- 概要：join からの射は固定した左因子と右因子の全標準単体で比較できる。
方針：coslice の curry の単体の等式から元の射の等式へ戻る。
規約：両因子と標的は任意。
使われ方：Kerodon §4.6.2 の二変数の比較。 -/
lemma join_right_hom_ext {A K X : SSet.{u}} {f g : join K A ⟶ X}
    (hK : joinInl K A ≫ f = joinInl K A ≫ g)
    (hA : ∀ n (a : (Δ[n] : SSet.{u}) ⟶ A), joinMap (𝟙 K) a ≫ f = joinMap (𝟙 K) a ≫ g) :
    f = g := by
  have h : sliceUnderCurry f rfl = sliceUnderCurry g hK.symm := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    exact hA n (SSet.yonedaEquiv.symm a)
  simpa only [sliceUnderUncurry_curry] using congrArg sliceUnderUncurry h

end SerrePositivity.InfinityCategories
