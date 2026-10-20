module

public import SerrePositivity.EInfinity.FrameHom.ThreeArrowLeftReplacement
public import SerrePositivity.EInfinity.FrameHom.ThreeArrowRightReplacement
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 特殊な三本矢と弱同値の両脚を持つ三本矢の比較

概要：元の特殊な三本矢の包含の nerve そのものが弱ホモトピー同値となる。
方針：左脚と右脚の関手的置換による二つの充満忠実な包含の反転性を合成。
規約：元のモデル圏と指定した関手的分解を使い、元の対象の cofibrancy は要求しない。
使われ方：Low 命題3.5 の特殊な三本矢から一般の三本矢への工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.EInfinity.FrameHom.WeakThreeArrow
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 元の両脚・中間射・全縦射を保持する特殊な三本矢からの包含。 -/
abbrev inclusion (X Y : C) : SpecialHammock X Y ⥤ WeakThreeArrow X Y :=
  ArrowSpan.inclusion (fun _ _ _ h => h.2) (fun _ _ _ h => h.2)

/-- 二つの片脚の包含の合成は同じ元の包含。 -/
lemma inclusion_fac (X Y : C) :
    (specialInclusion : SpecialHammock X Y ⥤ LeftTrivialThreeArrow X Y) ⋙ leftInclusion =
      inclusion X Y := rfl

/-- 元の特殊な三本矢の包含の nerve そのものは anodyne 局所化で可逆。 -/
lemma inclusion_localized_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (inclusion X Y))) := by
  have := LeftReplacement.inclusion_localized_isIso cof (X := X) (Y := Y)
  have := RightReplacement.inclusion_localized_isIso fib (X := X) (Y := Y)
  rw [← inclusion_fac]
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (nerveMap (specialInclusion : SpecialHammock X Y ⥤ LeftTrivialThreeArrow X Y) ≫
      nerveMap leftInclusion))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 同じ元の包含は、元の両 nerve の Kan 性なしで弱ホモトピー同値。 -/
lemma inclusion_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence (nerveMap (inclusion X Y)) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _ (inclusion_localized_isIso cof fib X Y)

end SerrePositivity.EInfinity.FrameHom.WeakThreeArrow
