module

public import SerrePositivity.InfinityCategories.F2.ReplacementPathHomotopySection
public import SerrePositivity.InfinityCategories.F2.EquivalenceHomotopyFixedPrecomposition

/-!
概要：path 置換の切断上の元の指定関手同型の簡約。
方針：可縮 fiber による比較の一意性と構成の端点の輸送を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y : SSet.{u}} [Quasicategory Y]
/-- 概要：path 置換の切断上の元の指定関手同型の簡約。
方針：可縮 fiber による比較の一意性と構成の端点の輸送を使う。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma equivalencePathReplacementFunctorIso_heq (f : X ⟶ Y) :
    HEq (equivalencePathReplacementFunctorIso f)
      (functorIsoOfEquivalenceHomotopy (replacementPathHomotopy f)
        (replacementPathHomotopy_invertible f)) := by
  have hfiber : HEq (equivalencePathReplacementFunctorIso f)
      (FunctorIso.postcomp
        (equivalenceHomotopyFiberIso (replacementPathHomotopy f)
          (replacementPathHomotopy_invertible f)).symm (equivalencePathEndpoint Y 1)) := by
    unfold equivalencePathReplacementFunctorIso
    exact (cast_heq _ _).trans ((cast_heq _ _).trans ((cast_heq _ _).trans (HEq.refl _)))
  exact hfiber.trans (functorIsoOfEquivalenceHomotopy_heq (replacementPathHomotopy f)
    (replacementPathHomotopy_invertible f)).symm
/-- 概要：path 置換の切断上の元の指定関手同型の簡約。
方針：可縮 fiber による比較の一意性と構成の端点の輸送を使う。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma equivalencePathReplacementFunctorIso_section_precomp_isFunctorEqIso
    {D : SSet.{u}} (f : X ⟶ Y) (a : D ⟶ X) :
    IsFunctorEqIso ((equivalencePathReplacementFunctorIso f).precomp
      (a ≫ equivalencePathReplacementSection f)) := by
  have hr := congrArg (fun k ↦ a ≫ k) (replacementPathHomotopy_section f)
  have he := equivalenceHomotopyIso_fixed_precomp (replacementPathHomotopy f)
    (replacementPathHomotopy_invertible f) (a ≫ equivalencePathReplacementSection f) hr
  have h₀ := replacementPathHomotopy_zero f
  have h₁ := replacementPathHomotopy_one f
  have hh := functorIso_precomp_heq_of_heq _ _ h₀ h₁
    (equivalencePathReplacementFunctorIso_heq f) (a ≫ equivalencePathReplacementSection f)
  exact he.of_heq (congrArg (fun k ↦ (a ≫ equivalencePathReplacementSection f) ≫ k) h₀)
    (congrArg (fun k ↦ (a ≫ equivalencePathReplacementSection f) ≫ k) h₁) hh

end SerrePositivity.InfinityCategories.F2
