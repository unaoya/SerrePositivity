module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality

/-!
概要：内部 Hom の交換同型の第二の源に関する自然性。
方針：二重評価とテンソル因子の交換の自然性を使う。
規約：源の射に単射性を要求しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。円の自己射のパラメータつき作用。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

omit [MonoidalClosed C] in
/-- 概要：テンソル交換の中央の因子に関する自然性。
方針：結合子と braiding の自然性を順に適用する。
規約：源の射 i は任意。
使われ方：HA §1.4.2、BF 1978 §2。二重評価の源の制限の比較。 -/
@[reassoc]
theorem exchange_natural_middle (A : C) {K L : C} (i : K ⟶ L) (Z : C) :
    A ◁ (i ▷ Z) ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A L Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K Z).hom ≫ i ▷ (A ⊗ Z) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorRight, Functor.flip, curriedTensor, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left]

/-- 概要：内部 Hom の交換は第二の源の射による制限と可換。
方針：二重評価の後で、制限と評価の式および因子交換の自然性を使う。
規約：i は任意の射 K→L。
使われ方：Goerss–Jardine I §7、HA §1.4.2。円の自己射と全パラメータの交換。 -/
@[reassoc]
theorem natural_pre_right (A : C) {K L : C} (i : K ⟶ L) (Y : C) :
    (ihom A).map ((MonoidalClosed.pre i).app Y) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A L Y).hom ≫ (MonoidalClosed.pre i).app ((ihom A).obj Y) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  have he : A ◁ (ihom A).map ((MonoidalClosed.pre i).app Y) ≫
      (ihom.ev A).app ((ihom K).obj Y) =
      (ihom.ev A).app ((ihom L).obj Y) ≫ (MonoidalClosed.pre i).app Y :=
    (ihom.ev A).naturality _
  rw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp, Category.assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev]
  have hw := whisker_exchange i ((ihom.ev A).app ((ihom L).obj Y))
  have hc := congrArg (fun f =>
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K ((ihom A).obj ((ihom L).obj Y))).hom ≫
      f ≫ (ihom.ev L).app Y) hw
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K ((ihom A).obj ((ihom L).obj Y))).hom ≫
        i ▷ (A ⊗ (ihom A).obj ((ihom L).obj Y)) ≫
          L ◁ (ihom.ev A).app ((ihom L).obj Y) ≫ (ihom.ev L).app Y := by
      simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj, tensorLeft, Functor.flip,
        curriedTensor] using hc
    _ = _ := by rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.exchange_natural_middle_assoc]

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
