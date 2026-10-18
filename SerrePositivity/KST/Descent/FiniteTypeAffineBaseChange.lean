module

public import SerrePositivity.KST.Descent.AffineSchemeBaseChange
public import SerrePositivity.KST.Descent.FiniteTypeLimitPreservation
public import SerrePositivity.KST.Descent.FiniteTypeAction

/-!
# 有限型の圏の実際のアフィン底変換の推移性

## 概要
アフィン基底変更の推移性を、元の前層の定義域内の指定引き戻しへ移す。

## 方針
忘却が保つ Cartesian 正方形の標準同型を同変に比較し、点の推移性を反映する。

## 規約
作用は有限型の圏の pullbackAction を使う。底変換の点の推移性は結論として導出する。

## 使われ方
論文 補題 3.2 の実際の Čech 各段への切断つき全次数降下の適用。
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

/-- 概要：有限型の圏内のアフィン射の底変換の指定作用（論文 補題 3.2）。
方針：元のアフィン始域に作用し、底変換側を固定する。
規約：実際の指定引き戻しへの既存の作用。
使われ方：Čech 各段への比較の指定作用。 -/
noncomputable def affineFiniteTypeBaseChangeAction : G →* Aut
    (pullback (affineAlgebraOverProjection (T := T) a) k) :=
  pullbackAction _ k (affineAlgebraOverAction (G := G) a) 1 1
    (fun g ↦ (affineAlgebraOverAction_over_base a g).trans (Category.comp_id _).symm)
    (fun _ ↦ (Category.id_comp k).trans (Category.comp_id k).symm)

/-- 概要：実際の有限型アフィン底変換で点のファイバーは推移的（論文 補題 3.2）。
方針：underlying scheme の実際の引き戻しへ同変な標準同型で移して戻す。
規約：元の環論的な幾何的推移性から導き、段ごとの推移性は仮定しない。
使われ方：各アフィン Čech 段での切断つき降下の幾何入力。 -/
theorem affineFiniteTypeBaseChange_transitive [IsAffine Z.obj.left]
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
    (affineSchemeBaseChange_transitive k.hom.left transitive) x y same_base

end SerrePositivity.KST.Descent
