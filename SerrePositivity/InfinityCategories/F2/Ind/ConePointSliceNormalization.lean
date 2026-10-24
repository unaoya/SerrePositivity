module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceBoundaryImage
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceBoundaryImage

/-!
概要：元の点写像を頂点の Yoneda 表示にすると、元の比較は従来の頂点表示の比較と一致する。
方針：同じ標準持ち上げと同じ指定逆像の定義を照合する。
規約：公開された元の比較の名前と型を保持する。
使われ方：任意の点写像での自然性と、既存の頂点表示の比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (SSet.yonedaEquiv.symm x))
  (hp : W ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b)
  (ht : joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (sliceIdentityCone x))
/-- 概要：元の点の境界比較は、頂点の Yoneda 表示で従来の同じ指定比較そのもの。
方針：元の定義を照合。規約：指定値の等号。使われ方：既存の頂点表示の比較の回収。 -/
lemma conePointSliceBoundaryRelativeIso_yoneda :
    conePointSliceBoundaryRelativeIso (SSet.yonedaEquiv.symm x) b hb W hp
      (by rw [ht, sliceOverUncurry_yoneda, Equiv.apply_symm_apply]; rfl) =
    coneTerminalSliceBoundaryRelativeIso x b hb W hp ht := rfl
/-- 概要：元の全 slice 族として読んでも、頂点表示で同じ境界比較を厳密に回収する。
方針：同じ元の包含で写す。規約：指定値の等号。使われ方：既存の全族比較との接続。 -/
lemma conePointSliceBoundaryFunctorIso_yoneda :
    conePointSliceBoundaryFunctorIso (SSet.yonedaEquiv.symm x) b hb W hp
      (by rw [ht, sliceOverUncurry_yoneda, Equiv.apply_symm_apply]; rfl) =
    coneTerminalSliceBoundaryFunctorIso x b hb W hp ht := rfl
end SerrePositivity.InfinityCategories.F2.Ind
