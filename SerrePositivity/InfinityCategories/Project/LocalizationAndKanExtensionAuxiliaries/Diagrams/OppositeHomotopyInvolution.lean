module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeInvolution
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyOppositeLaws

/-!
概要：二重反転した射と指定ホモトピーを異種等式で元へ戻す。
方針：反転関手の二乗の等式と、円柱の二重反転の公式を使う。
規約：異なる表示の始域・終域の同定を隠さない。
使われ方：指定右 Kan 変換を保持した双対化後の帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：二重反転した射は元の射と異種等式で一致する。
方針：反転関手の二乗の等式が与える射の共役の式を異種等式へ移す。
規約：対象の表示は同じ型であることを要求しない。
使われ方：Kan 拡張の三つの図式の二重反転の正規化。 -/
lemma opposite_map_map_heq {A D : SSet.{u}} (f : A ⟶ D) :
    HEq (SSet.opFunctor.map (SSet.opFunctor.map f)) f := by
  have h := CategoryTheory.Functor.congr_hom _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square f
  exact (conj_eqToHom_iff_heq _ _
    (CategoryTheory.Functor.congr_obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square A)
    (CategoryTheory.Functor.congr_obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square D)).1 h

/-- 概要：二重反転した指定ホモトピーの raw な射は元の射と異種等式で一致する。
方針：二重反転同型を等式による射と同定し、円柱の二重反転公式の共役を消す。
規約：元の指定ホモトピーそのものを回収する。
使われ方：左右 Kan 条件の双対化の逆方向。 -/
lemma homotopyOpposite_double_h_heq {A D : SSet.{u}} {f g : A ⟶ D}
    (H : SSet.Homotopy f g) : HEq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H)).h H.h := by
  have hi : (SSet.opFunctorCompOpFunctorIso.app A).inv =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq A).symm := by
    have he : SSet.opFunctorCompOpFunctorIso.app A = eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq A) :=
      Iso.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_doubleIso_eqToHom A)
    exact congrArg Iso.inv he
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyOpposite_double_h H
  rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_doubleIso_eqToHom] at h
  change (tensorRight (Δ[1] : SSet.{u})).map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq A).symm) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H)).h ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq D) = H.h at h
  rw [eqToHom_map] at h
  exact ((conj_eqToHom_iff_heq' H.h (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H)).h
    (congrArg (fun X : SSet.{u} ↦ X ⊗ (Δ[1] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq A).symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq D)).1 h.symm).symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
