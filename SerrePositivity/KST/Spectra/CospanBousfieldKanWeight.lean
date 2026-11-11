module

public import SerrePositivity.KST.Spectra.CospanOverWeightObjects
public import SerrePositivity.KST.Spectra.CospanLoopWeights

/-!
概要：通常の小さい cospan の BK 重みを、二辺のホーン重みに厳密に同定する。
方針：中央の over 圏の忘却と、両端の一点表示を自然同型に束ねる。
規約：構造射の向きも保持する。使われ方：BK end と loop の区間 end の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

/-- BK 重みの各対象を、元のホーンと外側の二頂点の重みへ同定する。 -/
def cospanBKWeightComponent (i : AsSmall.{u} WalkingCospan) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj i ≅ loopHornWeight.obj i :=
  match i with
  | ⟨none⟩ =>
      (nerveOverTerminalIso _ cospanOne_isTerminal).trans CospanShape.cospanNerveHornIso
  | ⟨some .left⟩ =>
      nerveSingletonIso (C := Over (AsSmall.up.obj .left : AsSmall.{u} WalkingCospan))
        (Over.mk (𝟙 _))
  | ⟨some .right⟩ =>
      nerveSingletonIso (C := Over (AsSmall.up.obj .right : AsSmall.{u} WalkingCospan))
        (Over.mk (𝟙 _))

/-- cospan の BK 重みは、二辺のホーン重みと自然同型。 -/
def cospanBKWeightIso : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ≅
    loopHornWeight :=
  NatIso.ofComponents cospanBKWeightComponent (by
    rintro ⟨a⟩ ⟨b⟩ ⟨f⟩
    change WidePullbackShape.Hom a b at f
    cases f with
    | id a =>
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).map
        (𝟙 (AsSmall.up.obj a)) ≫ _ = _ ≫ loopHornWeight.map (𝟙 (AsSmall.up.obj a))
      simp
    | term k =>
      apply SSet.hom_ext
      rintro ⟨⟨n⟩⟩
      apply ConcreteCategory.hom_ext
      intro σ
      apply Subtype.ext
      apply SSet.stdSimplex.ext
      intro i
      cases k <;>
        change CospanShape.cospanVertexIndex (σ.obj i).left = _
      all_goals
        have hσ := cospanOverEndpoint_eq _ (σ.obj i)
        have hleft := congrArg Over.left hσ
        rw [hleft]
      all_goals rfl)

/-- 中央の成分は、元の over 圏の忘却の nerve に続くホーンの座標表示。 -/
lemma cospanBKWeightIso_central_hom :
    cospanBKWeightIso.{u}.hom.app (AsSmall.up.obj .one) =
      nerveMap (Over.forget (AsSmall.up.obj .one : AsSmall.{u} WalkingCospan)) ≫
        CospanShape.cospanNerveHornIso.hom := rfl

/-- 左端の成分は、その over 圏の nerve から一点への唯一の射。 -/
lemma cospanBKWeightIso_left_hom :
    cospanBKWeightIso.{u}.hom.app (AsSmall.up.obj .left) =
      stdSimplex.isTerminalObj₀.from _ := rfl

/-- 右端の成分も、その over 圏の nerve から一点への唯一の射。 -/
lemma cospanBKWeightIso_right_hom :
    cospanBKWeightIso.{u}.hom.app (AsSmall.up.obj .right) =
      stdSimplex.isTerminalObj₀.from _ := rfl

end SerrePositivity.KST.Spectra
