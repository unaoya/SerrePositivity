module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeight
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveInitialComparison

/-!
概要：Bousfield–Kan 重みの補助重みへの包含は各成分で anodyne。
方針：I/i の終対象は始対象を付加しても終対象であり、包含の nerve は単射である。
規約：添字圏自体に始対象や終対象を要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の strict 極限の標準比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {C : Type u} [SmallCategory C]

/-- 概要：始対象を付加する包含の nerve は単射。
方針：包含後の射列の等式から対象と射を回収する。
規約：C の非空性も終対象性も不要。
使われ方：Kerodon 7.5.3（Tag 03AP） の補助重みの包含の単射性。 -/
lemma withInitialNerveInclusion_mono :
    Mono (nerveMap (WithInitial.incl : C ⥤ WithInitial C)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  change a ⋙ WithInitial.incl = b ⋙ WithInitial.incl at h
  have ho (i) : a.obj i = b.obj i := WithInitial.of.inj (Functor.congr_obj h i)
  refine CategoryTheory.Functor.ext ho ?_
  intro i j f
  apply (WithInitial.incl : C ⥤ WithInitial C).map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_map, Functor.comp_obj]
    using (Functor.congr_hom h f)

/-- 概要：元の圏の終対象は新しい始対象を付加しても終対象。
方針：元の対象からは元の一意な射、新しい始対象からは唯一の射を取る。
規約：元の対象の像 WithInitial.of c を終対象に指定する。
使われ方：Kerodon 7.5.3（Tag 03AP） の補助重みの共通の終対象。 -/
def withInitial_terminal {c : C} (hc : IsTerminal c) : IsTerminal (WithInitial.of c) := by
  refine IsTerminal.ofUniqueHom (fun X => match X with
    | WithInitial.of x => hc.from x
    | WithInitial.star => PUnit.unit) ?_
  intro X f
  cases X with
  | of x => exact hc.hom_ext _ _
  | star => exact Subsingleton.elim _ _

/-- 概要：right anodyne な射は Kan fibration の全てに対して持ち上げ性を持つ。
方針：全ホーンの持ち上げを零番目以外のホーンに制限し、右 fibration として使う。
規約：Kan–Quillen モデル構造の公理は使わない。
使われ方：Kerodon 7.5.3（Tag 03AP） の成分ごとの重みの anodyne 性。 -/
lemma anodyne_of_rightAnodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f) : anodyneExtensions f := by
  intro E D p hp
  have : Fibration p := ⟨hp⟩
  have h := (SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨by
    intro X Y j hj
    cases hj with
    | @intro n i hi => exact h _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ i)⟩
  exact hf p _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem

/-- 概要：終対象を持つ圏から始対象を付加した圏への包含の nerve は anodyne。
方針：共通の終対象を保つ単射の right anodyne 性を Kan fibration の持ち上げへ渡す。
規約：付加した始対象に既存の対象との同型は要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の over 圏の補助重みへの包含。 -/
lemma withInitialNerveInclusion_anodyne {c : C} (hc : IsTerminal c) :
    anodyneExtensions (nerveMap (WithInitial.incl : C ⥤ WithInitial C)) := by
  have := withInitialNerveInclusion_mono (C := C)
  exact anodyne_of_rightAnodyne _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_preservingTerminal_rightAnodyne WithInitial.incl hc (withInitial_terminal hc))

/-- 概要：Bousfield–Kan 重みから補助重みへの包含は各成分で anodyne。
方針：各 I/i の恒等射の対象が終対象であることを使う。
規約：I 自体の始対象性や終対象性は仮定しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、標準比較 κ の制限の同値性。 -/
lemma bousfieldKanConeWeightInclusion_anodyne {I : Type u} [SmallCategory I] (i : I) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion.app i) :=
  withInitialNerveInclusion_anodyne (Over.mkIdTerminal (X := i))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
