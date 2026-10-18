module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteShapeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralReflectedCriterion

/-!
概要：離散な小圏上の豊穣積と豊穣余積は coherent nerve の極限と余極限になる。
方針：反転 Hom 錐を終対象の重みと比較し、一般の native な判定へ渡す。
規約：通常の圏の極限性のみでなく全ての豊穣 Hom の極限性を要求する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、𝒮 の余積への共有界面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I] [IsDiscrete I]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：離散な小圏上の豊穣極限の反転比較 q′ は同型。
方針：反転 Hom 錐の極限性と終対象の重みの比較を使う。
規約：Hom の Kan 性を要求せず、反対の離散添字も許す。
使われ方：Kerodon 7.5.4.6、余積の Hom 条件からの比較。 -/
lemma reflectedRepresentableComparison_isDiscrete_isIso {F : I ⥤ C}
    (c : Cone F) (x : C) (hc : IsLimit (simplicialHomCone c x)) :
    IsIso (reflectedRepresentableComparison c x) :=
  weightedConeComparison_isIso_of_isTerminalWeight _ isDiscreteBousfieldKanWeight_isTerminal
    (reflectedSimplicialHomCone c x) (reflectedSimplicialHomCone_isLimit c x hc)

variable [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：離散な小圏上で全 Hom が極限を与える錐は native な極限錐。
方針：反転比較 q′ の厳密な同型性を一般の極限判定へ渡す。
規約：添字の有限性・非空性を要求しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の豊穣積。 -/
lemma strictCoherentCone_isLimit_of_isDiscrete_homLimit {F : I ⥤ C}
    (c : Cone F) (hc : ∀ x : C, IsLimit (simplicialHomCone c x)) :
    IsLimitCone (strictCoherentCone c) := by
  apply (strictCoherentCone_isLimit_iff_reflectedRepresentableComparison c).mpr
  intro x
  have := reflectedRepresentableComparison_isDiscrete_isIso c x (hc x)
  exact homotopyEquivalence_of_isIso _

/-- 概要：離散な小圏上で全ての反変 Hom が極限を与える余錐は native な余極限錐。
方針：反対の離散添字上の Hom の極限性を反対圏の錐に適用し、双対判定で戻す。
規約：元の標準図式上の strictNativeCocone を使い、通常の余極限性だけでは代用しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の豊穣余積から ∞ 余積への移送。 -/
lemma strictNativeCocone_isColimit_of_isDiscrete_homLimit {F : I ⥤ C}
    (c : Cocone F) (hc : ∀ x : Cᵒᵖ, IsLimit (simplicialHomCone c.op x)) :
    IsColimitCone (strictNativeCocone c) := by
  rw [strictNativeCocone_isColimit_iff]
  exact strictCoherentCone_isLimit_of_isDiscrete_homLimit c.op hc

end SerrePositivity.InfinityCategories.HomotopyLimits
