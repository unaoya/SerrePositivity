module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource

/-!
概要：持ち上げた随伴の評価による前合成は、パラメータの源制限と厳密に可換。
方針：反復 curry の源自然性と、持ち上げた随伴の制限式を使う。
規約：一般の閉モノイダル圏。使われ方：Kan 円上の全 Hom 自然性を通常の円へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomTensor
end SerrePositivity.KST.Spectra.InternalHomTensor
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 随伴の源を制限した同じ評価による前合成は、元の反復 Hom の源制限に一致する。 -/
lemma adjoint_pre_restriction {S K U V : C} (i : S ⟶ K) (a : U ⟶ (ihom K).obj V)
    (s : S ⊗ U ⟶ V) (ha : a ≫ (pre i).app V = curry s) (W : C) :
    (pre (uncurry a)).app W ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K U W).hom ≫
        (ihom U).map ((pre i).app W) =
      (pre s).app W ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S U W).hom := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left,
    ← Category.assoc, ← NatTrans.comp_app, ← pre_map]
  have h : i ▷ U ≫ uncurry a = s := by
    have h := congrArg uncurry ha
    rw [uncurry_pre_app, uncurry_curry] at h
    exact h
  rw [h]

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
