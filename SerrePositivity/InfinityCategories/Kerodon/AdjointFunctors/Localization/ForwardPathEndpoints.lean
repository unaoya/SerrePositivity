module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathPullbackNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathPushoutNaturality
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# forward ブロックの置換の元の端点の回収

概要：同時 pullback の終点と同時 pushout の始点は、指定した元の置換対象と同型。
方針：端点への元の合成が恒等射であることから、元の射影・包含の同型性を得る。
規約：同型の射は元の pullback.snd・pushout.inl。元の置換射と全比較に自然。
使われ方：左右の forward ブロックを同じ関手的分解の中間対象へ接続する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {n : ℕ}

section Pullback
variable [HasPullbacks C]

def pullbackEndpointIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackPath s).obj (Fin.last n) ≅ s.left := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg s.right (Fin.last n)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg_last]
    infer_instance
  exact asIso (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg s.right (Fin.last n)) s.hom)

lemma pullbackEndpointIso_fac (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) :
    (pullbackEndpointIso s).hom ≫ s.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackProjection s).app (Fin.last n) := by
  calc
    _ = pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg s.right (Fin.last n)) s.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg s.right (Fin.last n) := pullback.condition.symm
    _ = pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg s.right (Fin.last n)) s.hom ≫ 𝟙 _ :=
      congrArg (fun g => pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg s.right (Fin.last n)) s.hom ≫ g)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.terminalLeg_last s.right)
    _ = _ := Category.comp_id _

lemma pullbackEndpointIso_naturality {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n} (m : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparison m).app (Fin.last n) ≫ (pullbackEndpointIso t).hom =
      (pullbackEndpointIso s).hom ≫ m.left := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparisonApp_snd m (Fin.last n)

end Pullback

section Pushout
variable [HasPushouts C]

def pushoutEndpointIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) : s.right ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath s).obj 0 := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left 0) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg_zero]
    infer_instance
  exact asIso (pushout.inl s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left 0))

lemma pushoutEndpointIso_fac (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    s.hom ≫ (pushoutEndpointIso s).hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutInclusion s).app 0 := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left 0 ≫ pushout.inr s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left 0) := pushout.condition
    _ = 𝟙 _ ≫ pushout.inr s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left 0) :=
      congrArg (fun g => g ≫ pushout.inr s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left 0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg_zero s.left)
    _ = _ := Category.id_comp _

lemma pushoutEndpointIso_naturality {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t) :
    m.right ≫ (pushoutEndpointIso t).hom =
      (pushoutEndpointIso s).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutComparison m).app 0 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutComparisonApp_inl m 0).symm

end Pushout
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
