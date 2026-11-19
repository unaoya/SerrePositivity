module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：二つの内部 Hom の交換と単位からの内部 Hom の整合性。
方針：単位の比較を評価射で計算し、二重 uncurry とモノイダル整合性で確認する。
規約：一般の閉 braided 圏で述べる。
使われ方：HA §1.4.2、BF 1978 §2。定数族と loop の交換の計算。
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

omit [BraidedCategory C] in
/-- 概要：単位からの curry を標準同型で評価する一般式。
方針：標準同型を単位子と評価射で表し、随伴の三角恒等式を使う。
規約：通常の閉構造の単位同型。
使われ方：HA §1.4.2。定数族の単位の計算。 -/
theorem curry_unit_evaluation {A Y : C} (g : (𝟙_ C) ⊗ A ⟶ Y) :
    curry g ≫ (unitIsoSelf (X := Y)).hom = (λ_ A).inv ≫ g := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.unit_evaluation, leftUnitor_inv_naturality_assoc,
    whiskerLeft_curry_ihom_ev_app]

omit [BraidedCategory C] in
/-- 概要：単位からの内部 Hom の逆同型は左単位子の curry。
方針：標準同型を後合成して二つの単位子を相殺する。
規約：厳密な射の等式。
使われ方：HA §1.4.2。交換同型の単位での整合性。 -/
theorem unit_inv_eq_curry (Y : C) :
    (unitIsoSelf (X := Y)).inv = curry (λ_ Y).hom := by
  apply (cancel_mono (unitIsoSelf (X := Y)).hom).mp
  rw [Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.curry_unit_evaluation, Iso.inv_hom_id]

omit [MonoidalClosed C] in
/-- 概要：第二因子が単位のテンソル交換は左単位子と整合する。
方針：単位との braiding を単位子で表し、モノイダル整合性を使う。
規約：任意の閉 braided 圏。
使われ方：HA §1.4.2、BF 1978 §2。二重内部 Hom の単位の評価。 -/
@[reassoc]
theorem exchange_second_unit (A Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A (𝟙_ C) Z).hom ≫ (λ_ (A ⊗ Z)).hom = A ◁ (λ_ Z).hom := by
  have hb : (β_ A (𝟙_ C)).hom = (ρ_ A).hom ≫ (λ_ A).inv := by
    rw [← braiding_leftUnitor A, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor, hb, comp_whiskerRight, Category.assoc]
  monoidal

/-- 概要：内部 Hom の二つの源の交換は単位からの内部 Hom の逆同型と整合する。
方針：二重 uncurry で評価し、単位子とテンソル交換を相殺する。
規約：通常の点つき閉構造にも適用できる。
使われ方：HA §1.4.2、BF 1978 §2。定数族の end と loop の可換性。 -/
@[reassoc]
theorem natural_unit_inv (A Y : C) :
    (ihom A).map (unitIsoSelf (X := Y)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (𝟙_ C) Y).hom =
      (unitIsoSelf (X := (ihom A).obj Y)).inv := by
  apply uncurry_injective
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have he : A ◁ (ihom A).map (unitIsoSelf (X := Y)).inv ≫
      (ihom.ev A).app ((ihom (𝟙_ C)).obj Y) =
      (ihom.ev A).app Y ≫ (unitIsoSelf (X := Y)).inv :=
    (ihom.ev A).naturality _
  rw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.unit_inv_eq_curry, whiskerLeft_curry_ihom_ev_app]
  rw [leftUnitor_naturality, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.exchange_second_unit_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.unit_inv_eq_curry, uncurry_curry, uncurry_eq]

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
