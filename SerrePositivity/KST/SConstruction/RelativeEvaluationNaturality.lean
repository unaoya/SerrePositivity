module
public import SerrePositivity.KST.SConstruction.RelativeCofiberFunctor

/-! # 相対 cofiber 図式の二評価の自然性
概要：元の subobject・quotient の完全関手は相対入力に関して厳密に自然。
方針：両端の全部分圏の包含で検査し、周囲の cofiber 評価の自然性に帰着する。
規約：射の所属条件以外の仮定を追加しない。使われ方：相対加法性の自然変換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 相対 subobject の完全関手は相対入力に関して厳密に自然。 -/
lemma relativeCofiberSubobject_naturality {X Y : RelativeStableModel.{u}} (f : X ⟶ Y) :
    relativeCofiberMap f ≫ relativeCofiberSubobject Y.left Y.right =
      relativeCofiberSubobject X.left X.right ≫ relativeLeftFunctor.map f := by
  apply closedStableInclusion_cancel Y.left
  calc
    _ = relativeCofiberMap f ≫
        (relativeCofiberInclusion Y.left Y.right ≫ cofiberStableSubobject Y.ambient) :=
      (Category.assoc _ _ _).trans (congrArg (fun g => relativeCofiberMap f ≫ g)
        (relativeCofiberSubobject_inclusion Y.left Y.right))
    _ = (relativeCofiberInclusion X.left X.right ≫ cofiberEndofunctor.map f.val) ≫
        cofiberStableSubobject Y.ambient :=
      (Category.assoc _ _ _).symm.trans (congrArg
        (fun g => g ≫ cofiberStableSubobject Y.ambient) (relativeCofiberMap_inclusion f))
    _ = relativeCofiberInclusion X.left X.right ≫ (cofiberStableSubobject X.ambient ≫ f.val) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun g => relativeCofiberInclusion X.left X.right ≫ g)
        (cofiberSubobjectNat.naturality f.val))
    _ = (relativeCofiberSubobject X.left X.right ≫ closedStableInclusion X.left) ≫ f.val :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f.val)
        (relativeCofiberSubobject_inclusion X.left X.right).symm)
    _ = relativeCofiberSubobject X.left X.right ≫
        (relativeLeftFunctor.map f ≫ closedStableInclusion Y.left) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun g => relativeCofiberSubobject X.left X.right ≫ g)
        (closedStableMap_inclusion X.left Y.left f.val f.property.1).symm)
    _ = _ := (Category.assoc _ _ _).symm

/-- 相対 subobject を相対入力の圏上の自然変換に束ねる。 -/
def relativeCofiberSubobjectNat : relativeCofiberFunctor.{u} ⟶ relativeLeftFunctor where
  app X := relativeCofiberSubobject X.left X.right
  naturality {_X _Y} f := relativeCofiberSubobject_naturality f

/-- 相対 quotient の完全関手は相対入力に関して厳密に自然。 -/
lemma relativeCofiberQuotient_naturality {X Y : RelativeStableModel.{u}} (f : X ⟶ Y) :
    relativeCofiberMap f ≫ relativeCofiberQuotient Y.left Y.right =
      relativeCofiberQuotient X.left X.right ≫ relativeRightFunctor.map f := by
  apply closedStableInclusion_cancel Y.right
  calc
    _ = relativeCofiberMap f ≫
        (relativeCofiberInclusion Y.left Y.right ≫ cofiberStableQuotient Y.ambient) :=
      (Category.assoc _ _ _).trans (congrArg (fun g => relativeCofiberMap f ≫ g)
        (relativeCofiberQuotient_inclusion Y.left Y.right))
    _ = (relativeCofiberInclusion X.left X.right ≫ cofiberEndofunctor.map f.val) ≫
        cofiberStableQuotient Y.ambient :=
      (Category.assoc _ _ _).symm.trans (congrArg
        (fun g => g ≫ cofiberStableQuotient Y.ambient) (relativeCofiberMap_inclusion f))
    _ = relativeCofiberInclusion X.left X.right ≫ (cofiberStableQuotient X.ambient ≫ f.val) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun g => relativeCofiberInclusion X.left X.right ≫ g)
        (cofiberQuotientNat.naturality f.val))
    _ = (relativeCofiberQuotient X.left X.right ≫ closedStableInclusion X.right) ≫ f.val :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f.val)
        (relativeCofiberQuotient_inclusion X.left X.right).symm)
    _ = relativeCofiberQuotient X.left X.right ≫
        (relativeRightFunctor.map f ≫ closedStableInclusion Y.right) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun g => relativeCofiberQuotient X.left X.right ≫ g)
        (closedStableMap_inclusion X.right Y.right f.val f.property.2).symm)
    _ = _ := (Category.assoc _ _ _).symm

/-- 相対 quotient を相対入力の圏上の自然変換に束ねる。 -/
def relativeCofiberQuotientNat : relativeCofiberFunctor.{u} ⟶ relativeRightFunctor where
  app X := relativeCofiberQuotient X.left X.right
  naturality {_X _Y} f := relativeCofiberQuotient_naturality f

end SerrePositivity.KST.SConstruction
