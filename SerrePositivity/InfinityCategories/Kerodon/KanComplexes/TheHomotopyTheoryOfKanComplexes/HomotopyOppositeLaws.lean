module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：指定ホモトピーの反転は前後合成と可換で、二重反転から元へ戻る。
方針：反転した円柱の自然性と二重反転の公式を使う。
規約：ホモトピーの類ではなく実際の円柱の射を比較する。
使われ方：反転した comma への持ち上げで元の指定変換を回収する。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：指定ホモトピーの反転はパラメータの前合成と可換。
方針：反転したパラメータへの射を円柱の第二因子へ移す。
規約：端点の等式を別途輸送せず raw な射を扱う。
使われ方：comma の普遍変換を指定した族へ制限する。 -/
lemma kanHomotopyOpposite_precomp_h {A B X : SSet.{u}} {f g : B ⟶ X}
    (H : SSet.Homotopy f g) (i : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i)).h =
      (SSet.opFunctor.map i ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H).h := rfl

/-- 概要：指定ホモトピーの反転は値域の後合成と可換。
方針：反転を後合成に分配する。
規約：値域の射は任意。
使われ方：反転後の標準変換を二重反転の同型で元の値域へ戻す。 -/
lemma kanHomotopyOpposite_postcomp_h {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q)).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H).h ≫ SSet.opFunctor.map q := rfl

/-- 概要：指定ホモトピーの二重反転を元の始域と標的へ戻すと元の射になる。
方針：時間の因子を第一因子へ直して円柱の二重反転を消去する。
規約：始域側には二重反転の同型の逆を前合成する。
使われ方：oriented comma の持ち上げから元の指定変換を回収する。 -/
lemma kanHomotopyOpposite_double_h {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) :
    ((SSet.opFunctorCompOpFunctorIso.app A).inv ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H)).h ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom = H.h := by
  apply (cancel_epi (β_ (Δ[1] : SSet.{u}) A).hom).1
  change ((Δ[1] : SSet.{u}) ◁ (SSet.opFunctorCompOpFunctorIso.app A).inv) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)) ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_double]
  simp only [← Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id,
    Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
