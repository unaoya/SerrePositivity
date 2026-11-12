module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange

/-!
概要：二つの内部 Hom の交換同型の源の射に関する自然性。
方針：二重に評価し、テンソル交換と指数の制限の評価式を使う。
規約：源の射に単射性を要求しない。
使われ方：BF 1978 §2、HA §1.4.2。パラメータを持つ loop のホモトピー類の自然性。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 概要：内部 Hom の交換は最初の源の射による制限と可換。
方針：二重評価を展開して、制限の評価式とテンソル交換の源の自然性を比較する。
規約：i は任意の射 A→B。
使われ方：HA §1.4.2、BF 1978 §2。loop を値とする写像の成分のパラメータ変数の自然性。 -/
@[reassoc]
theorem natural_pre_left {A B : C} (i : A ⟶ B) (K Y : C) :
    (MonoidalClosed.pre i).app ((ihom K).obj Y) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B K Y).hom ≫ (ihom K).map ((MonoidalClosed.pre i).app Y) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  have he : A ◁ (MonoidalClosed.pre i).app ((ihom K).obj Y) ≫
      (ihom.ev A).app ((ihom K).obj Y) =
      i ▷ ((ihom B).obj ((ihom K).obj Y)) ≫ (ihom.ev B).app ((ihom K).obj Y) :=
    MonoidalClosed.id_tensor_pre_app_comp_ev _ _
  rw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_left_assoc]

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.natural_pre_left := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.natural_pre_left_assoc := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left_assoc
