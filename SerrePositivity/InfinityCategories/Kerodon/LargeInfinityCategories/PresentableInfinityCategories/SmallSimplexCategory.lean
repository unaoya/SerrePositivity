module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallShapeSimplices
public import Mathlib.CategoryTheory.Comma.CardinalArrow

/-!
概要：μ-small な単体集合の単体圏の、全ての射を含む小ささを評価する。
方針：全単体を対象とし、各有限な単体作用の集合を正則性で合計する。
規約：対象の個数だけでなく Arrow の個数を評価する。
使われ方：密度表示と μ-small な通常の極限・余極限。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 非可算正則 μ について、元の単体圏の対象の総数は μ 未満。 -/
lemma hasCardinalLT_simplexCategory {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) :
    HasCardinalLT K.Elements μ := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_allSimplices_of_isKappaSmall hμ hK).of_surjective
    S.equivElements S.equivElements.surjective

/-- 非可算正則 μ について、単体圏の全射の総数も同じ μ 未満。 -/
lemma hasCardinalLT_simplexCategory_arrow {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) :
    HasCardinalLT (Arrow K.Elements) μ := by
  have hE := hasCardinalLT_simplexCategory hμ hK
  have hHom (x y : K.Elements) : HasCardinalLT (x ⟶ y) μ := by
    have : Finite (y.obj.unop ⟶ x.obj.unop) :=
      Finite.of_equiv ((stdSimplex.{u}.obj x.obj.unop).obj y.obj) stdSimplex.objEquiv
    have : Finite (x.obj ⟶ y.obj) := Finite.of_injective (fun f ↦ f.unop) (by
      intro f g h
      simpa using congrArg Quiver.Hom.op h)
    have : Finite (x ⟶ y) := Finite.of_injective (fun f ↦ f.hom) (by
      intro f g h
      cases f
      cases g
      cases h
      rfl)
    exact hasCardinalLT_of_finite _ _ hμ.le
  have hAll : HasCardinalLT (Σ x : K.Elements, Σ y : K.Elements, (x ⟶ y)) μ :=
    hasCardinalLT_sigma _ μ hE (fun x ↦ hasCardinalLT_sigma _ μ hE (hHom x))
  exact hAll.of_surjective (Arrow.equivSigma K.Elements).symm
    (Arrow.equivSigma K.Elements).symm.surjective

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
