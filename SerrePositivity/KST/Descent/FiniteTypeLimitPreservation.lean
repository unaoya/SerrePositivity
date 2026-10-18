module

public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import SerrePositivity.KST.Descent.BlowupGeometry
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# 有限型の圏の有限連結極限とスキームへの忘却

## 概要
Noether 基底上の有限型の圏からの忘却は、Čech に必要な有限連結極限を保つ。

## 方針
Over への包含が終対象と引き戻しを保つことを実際の幾何的モデルで検査する。
そこから有限極限の保存を得て、Over の忘却の連結極限の保存と合成する。

## 規約
スキームへの忘却は終対象を保つとは主張しない。値域の Tot とも区別する。

## 使われ方
論文 補題 3.2 の実際の Čech 各段のアフィン性と分離性の検査。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：有限型の圏から固定した基底上の Over への包含（論文 §3）。
方針：定義の充満部分圏の包含を使う。
規約：構造射も保持し、スキームだけへの忘却と区別する。
使われ方：Čech の幾何的な有限極限の保存。 -/
abbrev finiteTypeOverInclusion (S : Scheme.{u}) : FiniteTypeSchemes S ⥤ Over S :=
  ObjectProperty.ι (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

variable {S : Scheme.{u}} [IsNoetherian S]

/-- 概要：Over への包含は引き戻しを保つ（論文 補題 3.2）。
方針：構成済みの実際のモデルを両圏内の Cartesian 正方形にする。
規約：Noether 基底上の全ての有限型射を扱う。
使われ方：有限極限の保存の入力。 -/
noncomputable instance finiteTypeOverInclusion_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (finiteTypeOverInclusion S) := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro X Y Z f g _
  refine ⟨finiteTypePullback f g, finiteTypePullbackFst f g, finiteTypePullbackSnd f g,
    finiteTypePullback_isPullback f g, ?_⟩
  exact (IsPullback.of_hasPullback f.hom.left g.hom.left).of_map (Over.forget S)
    (congrArg (fun k ↦ k.hom) (finiteTypePullback_comm f g))

/-- 概要：Over への包含は有限極限を保つ（論文 補題 3.2）。
方針：基底の恒等構造射による終対象の保存と、引き戻しの保存を組み合わせる。
規約：スキームだけへの忘却の有限極限保存とは異なる。
使われ方：連結な Čech の各有限極限を忘却する前の段階。 -/
noncomputable instance finiteTypeOverInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (finiteTypeOverInclusion S) := by
  let : PreservesLimit (Functor.empty.{0} (FiniteTypeSchemes S)) (finiteTypeOverInclusion S) :=
    preservesLimit_of_preserves_limit_cone finiteTypeBaseIsTerminal
      ((isLimitMapConeEmptyConeEquiv (finiteTypeOverInclusion S)
        (finiteTypeBaseObject S)).symm Over.mkIdTerminal)
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (finiteTypeOverInclusion S) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- 概要：スキームへの忘却は有限連結極限を保つ（論文 補題 3.2）。
方針：有限型の圏の包含と Over の連結極限保存を合成する。
規約：空図式の極限の保存は主張しない。
使われ方：実際の Čech 各段を underlying scheme の極限として検査する。 -/
noncomputable instance finiteTypeSchemesForget_preservesFiniteConnectedLimits
    (J : Type v) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J (finiteTypeSchemesForget S) := by
  change PreservesLimitsOfShape J (finiteTypeOverInclusion S ⋙ Over.forget S)
  infer_instance

end SerrePositivity.KST.Descent
