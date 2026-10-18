module

public import SerrePositivity.KST.Spectra.WeightedCochains
public import SerrePositivity.KST.Spectra.GroupAction
public import Mathlib.RepresentationTheory.Homological.Resolution

/-!
概要：群作用の標準的な余単体 cochain 図式の点つき単体集合による構成。
方針：普遍被覆 EG の単体的な自由 G 集合を離散的な重みにし、同変内部 Hom を取る。
規約：このモジュールでは実際の余単体図式のみを構成し、Kan 性・hG との比較は別に証明する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。有理 Shapiro の余単体模型。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GroupActionCochains

/-- 概要：G 集合を離散的な単体集合の作用図式へ送る。
方針：離散単体集合の関手を作用の圏へ移し、一対象圏の図式として表示する。
規約：宇宙を揃えるため一対象圏を AsSmall で持ち上げる。
使われ方：Goerss–Jardine VIII §2。EG の各次数の重み。 -/
def actionWeightFunctor (G : Type u) [Group G] :
    Action (Type u) G ⥤ (AsSmall.{u} (SingleObj G) ⥤ SSet.{u}) :=
  (Functor.const (SimplexCategoryᵒᵖ) : Type u ⥤ SSet.{u}).mapAction G ⋙
    Action.FunctorCategoryEquivalence.functor ⋙
      (Functor.whiskeringLeft (AsSmall.{u} (SingleObj G)) (SingleObj G) SSet.{u}).obj AsSmall.down

/-- 概要：EG の各次数の自由 G 集合からなる実際の単体的な離散重み。
方針：Mathlib の普遍被覆 G^(n+1) の単体的図式を作用の離散重みへ送る。
規約：群の有限性は不要。顔・退化は普遍被覆の厳密な構造射。
使われ方：Goerss–Jardine VIII §2。同変 cochain の次数変化の源。 -/
def universalCoverWeight (G : Type u) [Group G] :
    SimplicialObject (AsSmall.{u} (SingleObj G) ⥤ SSet.{u}) :=
  classifyingSpaceUniversalCover G ⋙ actionWeightFunctor G

/-- 概要：スペクトルの厳密な群作用の一段の実際の余単体 cochain 図式。
方針：EG の単体的な離散重みから作用図式への点つき同変 end を取る。
規約：この定義だけから各値の Kan 性や Tot と hG の同型を主張しない。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群作用の余単体模型の各スペクトル段。 -/
def level {G : Type u} [Group G] (A : GroupAction.{u} G) (n : ℕ) :
    CosimplicialObject PointedSimplicialSet.{u} :=
  weightedCochains (universalCoverWeight G)
    (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙ OmegaSpectrum.levelEvaluation n)

end GroupActionCochains

end

end SerrePositivity.KST.Spectra
