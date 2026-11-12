module

public import SerrePositivity.EInfinity.Hammock.StageAttachmentDesc
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 元の長さ段階の境界による pushout 表示

概要：次段階は、前段階へ二つの最大交互語を元の境界に沿って貼った pushout である。
方針：境界上で整合する元の射の一意な延長を、余積の普遍性と組み合わせる。
規約：余積の添字は元の最大交互語であり、二つの初期方向と同値。proper 性を使う。
使われ方：Dwyer–Kan §4.3〜4.5 の段階ごとの弱同値の貼り合わせ。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (n : ℕ)

abbrev stageBoundarySum : SSet.{w} :=
  ∐ fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (lengthBoundary F n a.val).toFunctor

abbrev stageTopSum : SSet.{w} := ∐ fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val

def stageBoundarySumInclusion : stageBoundarySum F n ⟶ stageTopSum F n :=
  Sigma.desc (fun a => (lengthBoundary F n a.val).ι ≫ Sigma.ι (fun a => F.obj a.val) a)

def stageTopInclusion : stageTopSum F n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F (n + 1) :=
  Sigma.desc (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F (n + 1) a.val a.property.1.le)

lemma stageBoundarySumInclusion_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (lengthBoundary F n a.val).toFunctor) a ≫
        stageBoundarySumInclusion F n =
      (lengthBoundary F n a.val).ι ≫ Sigma.ι (fun a => F.obj a.val) a :=
  Sigma.ι_comp_desc _ a

lemma stageTopInclusion_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫ stageTopInclusion F n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F (n + 1) a.val a.property.1.le := Sigma.ι_comp_desc _ a

variable {F} (hF : ProperDiagram F)

def stageBoundaryAttach : stageBoundarySum F n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F n :=
  Sigma.desc (fun a => lengthBoundaryToStage hF n a.val)

lemma stageBoundaryAttach_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (lengthBoundary F n a.val).toFunctor) a ≫
        stageBoundaryAttach n hF = lengthBoundaryToStage hF n a.val := Sigma.ι_comp_desc _ a

lemma lengthStagePushout_condition :
    stageBoundaryAttach n hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F (Nat.le_succ n) =
      stageBoundarySumInclusion F n ≫ stageTopInclusion F n := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, stageBoundaryAttach_fac, ← Category.assoc,
    stageBoundarySumInclusion_fac, Category.assoc, stageTopInclusion_fac]
  exact lengthBoundary_square hF (Nat.le_succ n) a.val a.property.1.le

/-- 元の標準射からなる次段階の pushout 余錐。 -/
def lengthStagePushoutCocone : PushoutCocone (stageBoundaryAttach n hF)
    (stageBoundarySumInclusion F n) :=
  PushoutCocone.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F (Nat.le_succ n)) (stageTopInclusion F n)
    (lengthStagePushout_condition n hF)

def stageAttachmentDataOfPushoutCocone
    (s : PushoutCocone (stageBoundaryAttach n hF) (stageBoundarySumInclusion F n)) :
    StageAttachmentData hF n s.pt where
  lower := s.inl
  upper a := Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫ s.inr
  boundary a := by
    have he := congrArg (fun η => Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n =>
      (lengthBoundary F n a.val).toFunctor) a ≫ η) s.condition
    rw [← Category.assoc, stageBoundaryAttach_fac, ← Category.assoc,
      stageBoundarySumInclusion_fac, Category.assoc] at he
    exact he

/-- 境界で整合する射の一意な延長による、元の余錐の pushout の普遍性。 -/
def lengthStagePushout_isColimit : IsColimit (lengthStagePushoutCocone n hF) := by
  apply PushoutCocone.isColimitAux'
  intro s
  let d := stageAttachmentDataOfPushoutCocone n hF s
  refine ⟨stageAttachmentDesc d, stageAttachmentDesc_lower d, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro a
    change Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫
      (stageTopInclusion F n ≫ stageAttachmentDesc d) =
        Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫ s.inr
    rw [← Category.assoc, stageTopInclusion_fac, stageAttachmentDesc_upper]
    rfl
  · intro m hl hr
    apply stageAttachmentDesc_unique d m hl
    intro a
    have he := congrArg (fun η => Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n =>
      F.obj a.val) a ≫ η) hr
    change Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫
      (stageTopInclusion F n ≫ m) = _ at he
    rw [← Category.assoc, stageTopInclusion_fac] at he
    exact he

lemma lengthStage_isPushout : IsPushout (stageBoundaryAttach n hF)
    (stageBoundarySumInclusion F n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F (Nat.le_succ n))
      (stageTopInclusion F n) :=
  IsPushout.of_isColimit (lengthStagePushout_isColimit n hF)

end SerrePositivity.EInfinity.Hammock
