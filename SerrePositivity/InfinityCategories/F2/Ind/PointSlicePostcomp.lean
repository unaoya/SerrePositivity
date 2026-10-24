module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanIdentityVertex
public import SerrePositivity.InfinityCategories.Core.PinchedUniversal

/-!
概要：任意の元の関手による指定終点の slice の後合成を、終点を正規化して保持する。
方針：同じ全普遍錐を後合成し、指定された像の終点へ curry する。
規約：関手の fibration 性を仮定せず、恒等錐を厳密に保つ。
使われ方：充満忠実な関手の像で、局所 Kan 添字の恒等頂点の終対象性を示す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C D : SSet.{u}} (f : C ⟶ D) (y : C _⦋0⦌)

/-- 元の全普遍錐の後合成の終点は、元の指定頂点の像そのもの。 -/
lemma pointSlicePostcomp_fixed :
    joinInr (sliceOver (SSet.yonedaEquiv.symm y)) (Δ[0] : SSet.{u}) ≫
      (sliceOverUncurry (𝟙 (sliceOver (SSet.yonedaEquiv.symm y))) ≫ f) =
        SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y) := by
  rw [← Category.assoc, sliceOverUncurry_fixed, SSet.yonedaEquiv_symm_comp]

/-- 元の関手による slice の同じ全後合成を、元の像の終点で正規化する。 -/
def pointSlicePostcomp : sliceOver (SSet.yonedaEquiv.symm y) ⟶
    sliceOver (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y)) :=
  sliceOverCurry (sliceOverUncurry (𝟙 _) ≫ f) (pointSlicePostcomp_fixed f y)

/-- 同じ後合成は、始点の元の射影を保つ。 -/
lemma pointSlicePostcomp_projection :
    pointSlicePostcomp f y ≫ sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y)) =
      sliceOverProjection (SSet.yonedaEquiv.symm y) ≫ f := by
  rw [pointSlicePostcomp, sliceOverCurry_projection, ← Category.assoc,
    sliceOverUncurry_projection, Category.id_comp]

/-- 同じ後合成の全パラメータでの uncurry は、元の全錐の後合成そのもの。 -/
lemma pointSlicePostcomp_uncurry {A : SSet.{u}} (a : A ⟶ sliceOver (SSet.yonedaEquiv.symm y)) :
    sliceOverUncurry (a ≫ pointSlicePostcomp f y) = sliceOverUncurry a ≫ f := by
  rw [sliceOverUncurry_precomp, pointSlicePostcomp, sliceOverUncurry_curry,
    ← Category.assoc, ← sliceOverUncurry_precomp, Category.comp_id]

/-- 同じ後合成は、元の恒等錐を像の恒等錐そのものへ写す。 -/
lemma pointSlicePostcomp_identity :
    (pointSlicePostcomp f y).app (Opposite.op ⦋0⦌) (sliceIdentityCone y) =
      sliceIdentityCone (f.app (Opposite.op ⦋0⦌) y) := by
  apply SSet.yonedaEquiv.symm.injective
  apply sliceOverUncurry_injective
  have hy : SSet.yonedaEquiv.symm (sliceIdentityCone y) ≫ pointSlicePostcomp f y =
      SSet.yonedaEquiv.symm ((pointSlicePostcomp f y).app (Opposite.op ⦋0⦌)
        (sliceIdentityCone y)) := SSet.yonedaEquiv_symm_comp _ _
  rw [← hy, pointSlicePostcomp_uncurry,
    sliceOverUncurry_yoneda, sliceOverUncurry_yoneda]
  change (SSet.const y : join Δ[0] Δ[0] ⟶ C) ≫ f = _
  exact SSet.const_comp y f

end SerrePositivity.InfinityCategories.F2.Ind
