module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeightPointCorner
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeightAnodyne
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：始対象を持つ圏から終対象を持つ圏への埋め込みの nerve の anodyne 性。
方針：始域に終対象を付加し、始対象を保つ包含と終対象を保つ単射に分解する。
規約：関手の忠実性・対象上の単射性と、指定終対象が像にないことを明示する。
使われ方：Kerodon 4.7.3.22（Tag 02J5） とその双対、7.5.3.12 の cospan の重みの遷移。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：元の圏の始対象は新しい終対象を付加しても始対象。
方針：元の対象には元の一意な射を、新しい終対象には唯一の射を使う。
規約：元の対象の像 WithTerminal.of c を始対象に指定する。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
def withTerminal_initial {c : C} (hc : IsInitial c) : IsInitial (WithTerminal.of c) := by
  refine IsInitial.ofUniqueHom (fun X => match X with
    | WithTerminal.of x => hc.to x
    | WithTerminal.star => PUnit.unit) ?_
  intro X f
  cases X with
  | of x => exact hc.hom_ext _ _
  | star => exact Subsingleton.elim _ _
/-- 概要：終対象を付加する包含の nerve は単射。
方針：包含の忠実性と対象上の単射性を全射列へ移す。
規約：圏の非空性や始対象性は不要。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma withTerminalNerveInclusion_mono :
    Mono (nerveMap (WithTerminal.incl : C ⥤ WithTerminal C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful WithTerminal.incl (fun _ _ h => WithTerminal.of.inj h)
/-- 概要：像に指定終対象を含まない埋め込みをその終対象まで拡張しても nerve は単射。
方針：元の射と終対象への一意な射に分けて忠実性と対象上の単射性を確認する。
規約：F の忠実性と対象上の単射性、指定終対象が F の像にないことを要求する。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma nerveLiftToTerminal_mono (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) {t : D} (ht : IsTerminal t)
    (hmiss : ∀ c, F.obj c ≠ t) : Mono (nerveMap (WithTerminal.liftToTerminal F ht)) := by
  have : (WithTerminal.liftToTerminal F ht).Faithful :=
    { map_injective := fun {X Y} f g h => by
        cases X <;> cases Y
        · exact F.map_injective h
        · exact Subsingleton.elim _ _
        · exact PEmpty.elim f
        · exact Subsingleton.elim _ _ }
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful (WithTerminal.liftToTerminal F ht)
  intro X Y h
  cases X with
  | of x =>
    cases Y with
    | of y => exact congrArg WithTerminal.of (hF h)
    | star => exact (hmiss x h).elim
  | star =>
    cases Y with
    | of y => exact (hmiss y h.symm).elim
    | star => rfl
/-- 概要：始対象を持つ圏の埋め込みで終域の終対象を像に含まなければ nerve は anodyne。
方針：新しい終対象を付加し、始対象を保つ包含と終対象を保つ単射に分解して合成する。
規約：left と right の anodyne 性を全 Kan fibration に対する持ち上げ性へ移す。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma nerveMap_anodyne_of_initial_terminal (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) {c : C} (hc : IsInitial c)
    {t : D} (ht : IsTerminal t) (hmiss : ∀ x, F.obj x ≠ t) :
    anodyneExtensions (nerveMap F) := by
  let G := WithTerminal.liftToTerminal F ht
  have := withTerminalNerveInclusion_mono (C := C)
  have : Mono (nerveMap G) := nerveLiftToTerminal_mono F hF ht hmiss
  have hl : anodyneExtensions (nerveMap (WithTerminal.incl : C ⥤ WithTerminal C)) := by
    intro E B p hp
    have : Fibration p := ⟨hp⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_preservingInitial_leftAnodyne WithTerminal.incl hc
      (withTerminal_initial hc) p _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem
  have hr : anodyneExtensions (nerveMap G) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.anodyne_of_rightAnodyne _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_preservingTerminal_rightAnodyne G WithTerminal.starTerminal ht)
  have hcomp : nerveMap (WithTerminal.incl : C ⥤ WithTerminal C) ≫ nerveMap G =
      nerveMap F := rfl
  rw [← hcomp]
  exact anodyneExtensions.comp_mem _ _ hl hr

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
