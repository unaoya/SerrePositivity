module

public import SerrePositivity.KST.Descent.FiniteTypeLimitPreservation
public import SerrePositivity.KST.Descent.FiniteTypeCech
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# 実際のアフィン Čech 各段の幾何

## 概要
アフィンな始域・基底から作る実際の Čech 各段と、その底変換の始域はアフィンで分離的。

## 方針
有限連結極限の忘却による保存と、Mathlib のアフィン対象の極限のアフィン性を使う。

## 規約
同型なテンソル積の存在だけを仮定せず、指定された極限対象自体について証明する。
有限次元上界はアフィン性や Noether 性だけからは結論しない。

## 使われ方
論文 補題 3.2 の Čech 各段へ切断つき降下を適用するための幾何条件。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S]

/-- 概要：有限型の圏内のアフィン対象の有限連結極限はアフィン（論文 補題 3.2）。
方針：スキームへの忘却の極限保存後に、実際の極限錐のアフィン性を適用する。
規約：極限点は元の有限型の圏で指定した対象そのもの。
使われ方：Čech 各段および各段への底変換。 -/
theorem finiteTypeLimit_isAffine {J : Type v} [SmallCategory J] [FinCategory J] [IsConnected J]
    (D : J ⥤ FiniteTypeSchemes S) [HasLimit D]
    [∀ j, IsAffine (D.obj j).obj.left] : IsAffine (limit D).obj.left := by
  let F := finiteTypeSchemesForget S
  have (j : J) : IsAffine ((D ⋙ F).obj j) :=
    inferInstanceAs (IsAffine (D.obj j).obj.left)
  exact Scheme.isAffine_of_isLimit (F.mapCone (limit.cone D))
    (isLimitOfPreserves F (limit.isLimit D))

variable {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)
  [IsAffine X.obj.left] [IsAffine Y.obj.left]

/-- 概要：実際のアフィン Čech nerve の各非増強段はアフィン（論文 補題 3.2）。
方針：有限 wide pullback の図式の各頂点のアフィン性を検査する。
規約：元の前層の定義域内の実際の対象への instance。
使われ方：各段の座標環による幾何的推移性の適用。 -/
noncomputable instance finiteTypeCechStage_isAffine (n : SimplexCategoryᵒᵖ) :
    IsAffine ((finiteTypeAugmentedCech f).left.obj n).obj.left := by
  let D := WidePullbackShape.wideCospan Y (fun _ : Fin (n.unop.len + 1) ↦ X) (fun _ ↦ f)
  have (j : WidePullbackShape (Fin (n.unop.len + 1))) : IsAffine (D.obj j).obj.left := by
    cases j with
    | none => exact inferInstanceAs (IsAffine Y.obj.left)
    | some _ => exact inferInstanceAs (IsAffine X.obj.left)
  exact finiteTypeLimit_isAffine D

/-- 概要：実際の Čech 各段への底変換の始域もアフィン（論文 補題 3.2）。
方針：始域・Čech の段・基底からなる有限連結な cospan の極限を検査する。
規約：切断の存在や推移性はこのアフィン性には不要。
使われ方：切断つき降下の始域の分離性。 -/
noncomputable instance finiteTypeCechStageSource_isAffine (n : SimplexCategoryᵒᵖ) :
    IsAffine (finiteTypeCechStageArrow f n).left.obj.left := by
  let D := cospan f ((finiteTypeAugmentedCech f).hom.app n)
  have (j : WalkingCospan) : IsAffine (D.obj j).obj.left := by
    cases j with
    | none => exact inferInstanceAs (IsAffine Y.obj.left)
    | some i =>
      cases i
      · exact inferInstanceAs (IsAffine X.obj.left)
      · exact finiteTypeCechStage_isAffine f n
  exact finiteTypeLimit_isAffine D

/-- 概要：実際の Čech 各段への底変換の始域は S 上分離（論文 補題 3.2）。
方針：構成したアフィン性から絶対分離性を使う。
規約：S 自身の分離性を追加仮定にしない。
使われ方：完成した切断つき全次数降下の幾何入力。 -/
noncomputable instance finiteTypeCechStageSource_isSeparated (n : SimplexCategoryᵒᵖ) :
    IsSeparated (finiteTypeCechStageArrow f n).left.obj.hom := by
  have : IsAffine (finiteTypeCechStageArrow f n).left.obj.left :=
    finiteTypeCechStageSource_isAffine f n
  infer_instance

end SerrePositivity.KST.Descent
