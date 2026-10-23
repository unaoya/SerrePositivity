module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeConstFiberEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentConstantTargetComparison

/-!
概要：定値 unstraightening の相対 Hom 比較を元の pointed-space 評価と厳密に結ぶ。
方針：底変換・定値図式の表示変更・fiber 比較の三段階の評価を合成する。
規約：元の比較射を保ち、全パラメータで計算する。
使われ方：元の全 Hom の相対合成を fiber 上の写像の合成へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値標的の比較を評価して fiber に含めると元の pointed-space 成分と一致。
方針：各段階の相対 uncurry の評価式を使う。
規約：任意の底の図式と全パラメータ。使われ方：定値 fiber 上の合成の評価。 -/
lemma constantUnstraighteningRelativeIso_uncurry {A B T : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (k : T ⟶ relativeFunctorSpace
      (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)) a) :
    uncurry (k ≫ (constantUnstraighteningRelativeIso a z).hom) ≫
        vertexFiberι pointedSpaceProjection z =
      relativeFunctorUncurry k ≫ pullback.fst pointedSpaceProjection (SSet.const z : B ⟶ _) := by
  change uncurry (((k ≫ relativeFunctorBaseChangeForward pointedSpaceProjection
      (SSet.const z) a) ≫
        (eqToIso (congrArg (relativeFunctorSpace pointedSpaceProjection)
          (SSet.comp_const a z))).hom) ≫
            (relativeFunctorConstFiberIso pointedSpaceProjection z).hom) ≫
              vertexFiberι pointedSpaceProjection z = _
  rw [relativeConstFiberIso_uncurry,
    relativeFunctorUncurry_transport pointedSpaceProjection (SSet.comp_const a z),
    relativeFunctorBaseChangeForward_uncurry]

end SerrePositivity.InfinityCategories.F2
