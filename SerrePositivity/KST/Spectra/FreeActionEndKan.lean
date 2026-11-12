module

public import SerrePositivity.KST.Spectra.FreeActionEnd
public import SerrePositivity.KST.Spectra.PointedWeightedEnd
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：自由作用の重みを持つ同変 end の Kan 性と点つき模型への移送。
方針：軌道集合からの通常の内部 Hom の Kan 性を実際の同型で移す。
規約：係数の基礎単体集合の Kan 性だけを仮定する。
使われ方：Goerss–Jardine VIII §2。群作用の余単体 cochain の各値の Kan 性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed


namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 係数への自由作用の end は Kan 複体。
方針：軌道集合からの内部 Hom との同型で Kan 性を移す。
規約：群の有限性は不要。
使われ方：Goerss–Jardine VIII §2。同変 cochain の充填。 -/
instance end_kanComplex {G : Type u} [Group G] (S : Type u) (B : Action SSet.{u} G)
    [KanComplex B.V] : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) := by
  let : KanComplex ((ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj B.V) := inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (endIso S B).symm

/-- 概要：点つき単体集合の作用の実際の係数図式。
方針：小さな一対象圏上の点つき作用図式として表示する。
規約：各成分の値は B.V。
使われ方：Goerss–Jardine VIII §2。点つき同変 end の係数。 -/
abbrev pointedCoefficients {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G) :
    AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u} :=
  AsSmall.down ⋙ Action.FunctorCategoryEquivalence.functor.obj B

/-- 概要：自由作用の点つき end の基礎単体集合は Kan。
方針：点つき end の忘却比較と、自由作用の通常の end の内部 Hom 表示を合成する。
規約：基点は元の点つき作用の基点を保つ。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain 各次数の点つき Kan 性。 -/
lemma pointedEnd_kanComplex {G : Type u} [Group G] (S : Type u)
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] :
    KanComplex (PointedWeightedEnd.obj (weight S) (pointedCoefficients B)).right := by
  let D := (PointedSimplicialSet.forget.mapAction G).obj B
  let : KanComplex D.V := inferInstanceAs (KanComplex B.V.right)
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S)
      (pointedCoefficients B ⋙ PointedSimplicialSet.forget)) :=
    end_kanComplex S D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (PointedWeightedEnd.underlyingIso (weight S) (pointedCoefficients B)).symm

end

end SerrePositivity.KST.Spectra.FreeActionFamily
