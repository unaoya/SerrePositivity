module

public import SerrePositivity.KST.Descent.FiniteTypeCech
public import SerrePositivity.KST.Descent.EquivariantPullbackComparison

/-!
# 実際の Čech 底変換の各段の群作用と自然性

## 概要
元の射の基底上の群作用を、実際の Čech 各段での底変換へ移す。

## 方針
Čech の基底の段には自明作用を入れ、元の始域だけに群を作用させる。
外側の単体射からの底変換の射との同変性を二射影で検査する。

## 規約
元の Čech の座標への対角作用とは異なり、底変換した元の射のファイバーへの作用。

## 使われ方
論文 補題 3.2 の二重 Čech 図式の有理固定部分と、段ごとの切断つき降下。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) {G : Type u} [Group G] (action : G →* Aut X)
  (over_base : ∀ g, (action g).asIso.hom ≫ f = f)

/-- 概要：Čech 各段での底変換の始域の指定群作用（論文 補題 3.2）。
方針：元の始域の作用と、Čech の段・基底の自明作用を引き戻す。
規約：有限型の圏内の実際の指定引き戻しへの作用。
使われ方：各段の不変部分の指定比較。 -/
noncomputable def finiteTypeCechStageAction (n : SimplexCategoryᵒᵖ) :
    G →* Aut (finiteTypeCechStageArrow f n).left :=
  pullbackAction f ((finiteTypeAugmentedCech f).hom.app n) action 1 1
    (fun g ↦ (over_base g).trans (Category.comp_id f).symm)
    (fun _ ↦ (Category.id_comp _).trans (Category.comp_id _).symm)

/-- 概要：Čech 各段の作用は底変換の射の基底上にある（論文 補題 3.2）。
方針：引き戻しの第二射影の同変性と基底の自明作用を使う。
規約：全ての非増強段を扱う。
使われ方：段ごとの PiDescent の指定比較の定義。 -/
theorem finiteTypeCechStageAction_over_base (n : SimplexCategoryᵒᵖ) (g : G) :
    (finiteTypeCechStageAction f action over_base n g).asIso.hom ≫
        (finiteTypeCechStageArrow f n).hom = (finiteTypeCechStageArrow f n).hom := by
  exact (pullbackAction_snd f ((finiteTypeAugmentedCech f).hom.app n)
    action 1 1 _ _ g).trans (Category.comp_id _)

/-- 概要：Čech の外側の全ての単体射による底変換の射は同変（論文 補題 3.2）。
方針：二射影で検査し、左因子の恒等射と基底側の自明作用を使う。
規約：段ごとに選んだ切断の自然性は使わない。
使われ方：各段の不変部分の比較を一つの余単体図式に束ねる。 -/
theorem finiteTypeCechStageAction_naturality {n m : SimplexCategoryᵒᵖ}
    (α : n ⟶ m) (g : G) :
    (finiteTypeCechStageAction f action over_base n g).asIso.hom ≫
        ((finiteTypeCechBaseChange f).map α).left =
      ((finiteTypeCechBaseChange f).map α).left ≫
        (finiteTypeCechStageAction f action over_base m g).asIso.hom := by
  exact pullbackAction_map_trivialBase f ((finiteTypeAugmentedCech f).hom.app n)
    ((finiteTypeAugmentedCech f).hom.app m) action over_base
    ((finiteTypeAugmentedCech f).left.map α)
    (((finiteTypeAugmentedCech f).hom.naturality α).trans (Category.comp_id _)) g

/-- 概要：実際の Čech 各段の指定不変比較は外側の単体射について自然（論文 補題 3.2）。
方針：証明した底変換の射の同変性を、元の前層の指定比較の自然性へ渡す。
規約：全係数・全整数次数を保持し、段ごとの切断の自然性は使わない。
使われ方：各段の全次数降下を二重 Čech 図式の比較へ束ねる。 -/
theorem GradedPresheaf.finiteTypeCechStageComparison_naturality
    {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    (H : Coefficient) (k : ℤ) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (L.invariantPullback H k ((finiteTypeCechBaseChange f).map α).left
      (finiteTypeCechStageAction f action over_base n)
      (finiteTypeCechStageAction f action over_base m)
      (finiteTypeCechStageAction_naturality f action over_base α)).comp
        (L.invariantComparison H k (finiteTypeCechStageArrow f m).hom
          (finiteTypeCechStageAction f action over_base m)
          (finiteTypeCechStageAction_over_base f action over_base m)) =
      (L.invariantComparison H k (finiteTypeCechStageArrow f n).hom
        (finiteTypeCechStageAction f action over_base n)
        (finiteTypeCechStageAction_over_base f action over_base n)).comp
          (L.pullback H k ((finiteTypeAugmentedCech f).left.map α)) := by
  exact L.invariantComparison_naturality H k (finiteTypeCechStageArrow f m).hom
    (finiteTypeCechStageArrow f n).hom ((finiteTypeCechBaseChange f).map α).left
    ((finiteTypeCechBaseChange f).map α).right ((finiteTypeCechBaseChange f).map α).w
    (finiteTypeCechStageAction f action over_base m)
    (finiteTypeCechStageAction f action over_base n)
    (finiteTypeCechStageAction_over_base f action over_base m)
    (finiteTypeCechStageAction_over_base f action over_base n)
    (finiteTypeCechStageAction_naturality f action over_base α)

end SerrePositivity.KST.Descent
