module

public import SerrePositivity.KST.Descent.FiniteTypeAffineBaseChange
public import SerrePositivity.KST.Descent.FiniteTypeCechAction
public import SerrePositivity.KST.Descent.CechFiniteDimension
public import SerrePositivity.KST.Descent.SectionedDescent

/-!
# 実際のアフィン Čech 各段での全次数降下

## 概要
元の環の幾何的推移性から、実際の Čech 各段での底変換の全次数降下を導く。

## 方針
指定作用の点の推移性と、切断・アフィン性・分離性・局所 Noether 基底からの次元上界を供給する。

## 規約
段ごとの降下・推移性・有限次元上界を仮定に残さない。
元の射への Tot・Fubini による還元の完了は別工程。

## 使われ方
論文 補題 3.2 の τ 位相の層論を Čech 計算に置換する段ごとの入力。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {A T G : Type u}
  [CommRing A] [CommRing T] [Algebra A T] [Algebra.FiniteType A T]
  [Group G] [MulSemiringAction G T] [SMulCommClass G A T]
variable (a : Spec (.of A) ⟶ S) [LocallyOfFiniteType a] [QuasiCompact a]

local notation "p" => affineAlgebraOverProjection (T := T) a
local notation "act" => affineAlgebraOverAction (T := T) (G := G) a
local notation "overBase" => affineAlgebraOverAction_over_base (T := T) (G := G) a

/-- 概要：実際のアフィン Čech 各段で底変換の点のファイバーは推移的（論文 補題 3.2）。
方針：各段のアフィン性を導き、任意のアフィン基底変更の推移性を適用する。
規約：元の環の幾何的推移性から導出し、通常の点の推移性の底変換保存は仮定しない。
使われ方：切断つき降下の実際の各段への適用。 -/
theorem affineCechStage_transitive (transitive : IsGeometricallyTransitive A T G)
    (n : SimplexCategoryᵒᵖ) (x y : (finiteTypeCechStageArrow p n).left.obj.left)
    (same_base : (finiteTypeCechStageArrow p n).hom.hom.left x =
      (finiteTypeCechStageArrow p n).hom.hom.left y) :
    ∃ g : G, (finiteTypeCechStageAction p act overBase n g).asIso.hom.hom.left x = y := by
  have : IsAffine (affineAlgebraOverObject (T := T) a).obj.left :=
    inferInstanceAs (IsAffine (Spec (.of T)))
  have : IsAffine (affineOverObject a).obj.left := inferInstanceAs (IsAffine (Spec (.of A)))
  have hAffine : IsAffine ((finiteTypeAugmentedCech p).left.obj n).obj.left :=
    finiteTypeCechStage_isAffine p n
  exact @affineFiniteTypeBaseChange_transitive S _ A T G _ _ _ _ _ _ _ a _ _
    ((finiteTypeAugmentedCech p).left.obj n) ((finiteTypeAugmentedCech p).hom.app n)
    hAffine transitive x y same_base

/-- 概要：局所 Noether 基底で実際のアフィン Čech 各段は全次数降下を満たす（論文 補題 3.2）。
方針：切断・推移性・分離性・自然数の次元上界を実際に構成し、完成した帰納へ渡す。
規約：自然な blowup 列・有限積保存・冪零不変性は実降下から供給すべき条件として明示する。
使われ方：二重 Čech 図式を Tot で比較して元の射へ戻す際の段ごとの指定比較。 -/
theorem NaturalBlowupSequences.affineCechStage_piDescent
    [IsNoetherianRing A] [IsLocalRing A] {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G]
    (transitive : IsGeometricallyTransitive A T G) (n : SimplexCategoryᵒᵖ) :
    L.PiDescent (finiteTypeCechStageArrow p n).hom
      (finiteTypeCechStageAction p act overBase n)
      (finiteTypeCechStageAction_over_base p act overBase n) := by
  have : IsAffine (affineAlgebraOverObject (T := T) a).obj.left :=
    inferInstanceAs (IsAffine (Spec (.of T)))
  have : IsAffine (affineOverObject a).obj.left := inferInstanceAs (IsAffine (Spec (.of A)))
  have : IsSeparated (finiteTypeCechStageArrow p n).left.obj.hom :=
    finiteTypeCechStageSource_isSeparated p n
  obtain ⟨d, bound⟩ := localNoether_finiteTypeCechStage_dimension_bound a p n
  exact data.sectioned_piDescent (finiteTypeCechStageArrow p n).hom
    (finiteTypeCechStageAction p act overBase n)
    (finiteTypeCechStageAction_over_base p act overBase n)
    (finiteTypeCechStageSplitEpi p n).section_ (finiteTypeCechStageSplitEpi p n).id
    (affineCechStage_transitive a transitive n) d bound

end SerrePositivity.KST.Descent
