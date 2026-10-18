module

public import SerrePositivity.KST.Spectra.GroupActionCochains

/-!
概要：群作用の標準的な余単体 cochain の同変射に関する関手性。
方針：作用図式、各段の評価、重み付き cochain の関手を合成する。
規約：対象も射も実際の点つき余単体図式。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。hG の余単体模型の係数比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：群作用の cochain の一段は同変な BF 射に関する関手。
方針：作用を図式へ送り、段評価と小圏の持ち上げを経て cochain 関手を適用する。
規約：ここでは Kan 性や hG の同型性は主張しない。
使われ方：Goerss–Jardine VIII §2。作用スペクトルの射の余単体模型。 -/
def levelFunctor (G : Type u) [Group G] (n : ℕ) :
    GroupAction.{u} G ⥤ CosimplicialObject PointedSimplicialSet.{u} :=
  GroupAction.diagramFunctor G ⋙
    (Functor.whiskeringRight (SingleObj G) OmegaSpectrum.{u} PointedSimplicialSet.{u}).obj
      (OmegaSpectrum.levelEvaluation n) ⋙
    (Functor.whiskeringLeft (AsSmall.{u} (SingleObj G)) (SingleObj G)
      PointedSimplicialSet.{u}).obj AsSmall.down ⋙
    weightedCochainsFunctor (universalCoverWeight G)

/-- 概要：同変な BF 射が誘導する一段の余単体 cochain の射。
方針：合成関手の射を取り出す。
規約：始域と終域は既存の level の実際の余単体図式。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。作用の比較射を cochain へ送る。 -/
def levelMap {G : Type u} [Group G] {A B : GroupAction.{u} G} (f : A ⟶ B) (n : ℕ) :
    level A n ⟶ level B n :=
  (levelFunctor G n).map f

end

end SerrePositivity.KST.Spectra.GroupActionCochains
