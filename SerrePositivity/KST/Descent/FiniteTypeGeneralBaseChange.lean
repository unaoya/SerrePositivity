module

public import SerrePositivity.KST.Descent.FiniteTypeAffineBaseChange
public import SerrePositivity.KST.Descent.GeneralSchemeBaseChange

/-!
# 有限型スキームへの一般の底変換の推移性

## 概要
アフィン性を仮定せず、有限型の圏の指定引き戻しでファイバーの推移性を示す。

## 方針
忘却が保つ Cartesian 正方形を同変に比較し、任意のスキームへの底変換の結果を戻す。

## 規約
幾何的推移性は元の環拡大にだけ課す。底変換後の推移性は結論である。

## 使われ方
論文 補題 3.2・3.3、定理 3.1 の blowup と閉中心を含む降下。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {A T G : Type u}
  [CommRing A] [CommRing T] [Algebra A T] [Algebra.FiniteType A T]
  [Group G] [MulSemiringAction G T] [SMulCommClass G A T]
variable (a : Spec (.of A) ⟶ S) [LocallyOfFiniteType a] [QuasiCompact a]
  {Z : FiniteTypeSchemes S} (k : Z ⟶ affineOverObject a)

/-- 概要：任意の有限型スキームへの実際の底変換で点のファイバーは推移的（論文 補題 3.2）。
方針：underlying scheme の実際の引き戻しへ同変な標準同型で移して戻す。
規約：元の環論的な幾何的推移性から導き、段ごとの推移性は仮定しない。
使われ方：blowup・中心を含む各 Čech 段での切断つき降下の幾何入力。 -/
theorem finiteTypeBaseChange_transitive
    (transitive : IsGeometricallyTransitive A T G)
    (x y : (pullback (affineAlgebraOverProjection (T := T) a) k).obj.left)
    (same_base : (pullback.snd (affineAlgebraOverProjection (T := T) a) k).hom.left x =
      (pullback.snd (affineAlgebraOverProjection (T := T) a) k).hom.left y) :
    ∃ g : G,
      (affineFiniteTypeBaseChangeAction (T := T) (G := G) a k g).asIso.hom.hom.left x = y := by
  let f := affineAlgebraOverProjection (T := T) a
  let F := finiteTypeSchemesForget S
  let act := affineFiniteTypeBaseChangeAction (T := T) (G := G) a k
  have square : IsPullback (F.map (pullback.fst f k)) (F.map (pullback.snd f k))
      (F.map f) (F.map k) := (IsPullback.of_hasPullback f k).map F
  have first (g : G) : (finiteTypeUnderlyingAction act g).asIso.hom ≫
      F.map (pullback.fst f k) = F.map (pullback.fst f k) ≫ (specAction g).asIso.hom :=
    congrArg (fun h ↦ F.map h)
      (pullbackAction_fst f k (affineAlgebraOverAction a) 1 1 _ _ g)
  have second (g : G) : (finiteTypeUnderlyingAction act g).asIso.hom ≫
      F.map (pullback.snd f k) = F.map (pullback.snd f k) ≫ 𝟙 Z.obj.left :=
    congrArg (fun h ↦ F.map h)
      (pullbackAction_snd f k (affineAlgebraOverAction a) 1 1 _ _ g)
  have equivariant (g : G) : (finiteTypeUnderlyingAction act g).asIso.hom ≫
      square.isoPullback.hom = square.isoPullback.hom ≫
        (affineSchemeBaseChangeAction (T := T) k.hom.left g).asIso.hom := by
    exact isPullback_isoPullback_equivariant square (finiteTypeUnderlyingAction act)
      specAction 1 1
      (fun g ↦ (specAction_over_base g).trans (Category.comp_id _).symm)
      (fun _ ↦ (Category.id_comp _).trans (Category.comp_id _).symm) first second g
  exact schemeFiberTransitivity_of_injective_square (pullback.snd _ _)
    (F.map (pullback.snd f k)) square.isoPullback.hom (𝟙 _)
    (square.isoPullback_hom_snd.trans (Category.comp_id _).symm)
    (affineSchemeBaseChangeAction k.hom.left) (finiteTypeUnderlyingAction act) equivariant
    square.isoPullback.hom.homeomorph.injective
    (schemeBaseChange_transitive k.hom.left transitive) x y same_base

end SerrePositivity.KST.Descent
