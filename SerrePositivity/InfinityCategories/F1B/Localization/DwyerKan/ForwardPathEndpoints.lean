module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathPullbackNaturality
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathPushoutNaturality
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# forward ブロックの置換の元の端点の回収

概要：同時 pullback の終点と同時 pushout の始点は、指定した元の置換対象と同型。
方針：端点への元の合成が恒等射であることから、元の射影・包含の同型性を得る。
規約：同型の射は元の pullback.snd・pushout.inl。元の置換射と全比較に自然。
使われ方：左右の forward ブロックを同じ関手的分解の中間対象へ接続する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {n : ℕ}

section Pullback
variable [HasPullbacks C]

def pullbackEndpointIso (s : TerminalReplacement C n) :
    (pullbackPath s).obj (Fin.last n) ≅ s.left := by
  have : IsIso (terminalLeg s.right (Fin.last n)) := by
    rw [terminalLeg_last]
    infer_instance
  exact asIso (pullback.snd (terminalLeg s.right (Fin.last n)) s.hom)

lemma pullbackEndpointIso_fac (s : TerminalReplacement C n) :
    (pullbackEndpointIso s).hom ≫ s.hom = (pullbackProjection s).app (Fin.last n) := by
  calc
    _ = pullback.fst (terminalLeg s.right (Fin.last n)) s.hom ≫
        terminalLeg s.right (Fin.last n) := pullback.condition.symm
    _ = pullback.fst (terminalLeg s.right (Fin.last n)) s.hom ≫ 𝟙 _ :=
      congrArg (fun g => pullback.fst (terminalLeg s.right (Fin.last n)) s.hom ≫ g)
        (terminalLeg_last s.right)
    _ = _ := Category.comp_id _

lemma pullbackEndpointIso_naturality {s t : TerminalReplacement C n} (m : s ⟶ t) :
    (pullbackComparison m).app (Fin.last n) ≫ (pullbackEndpointIso t).hom =
      (pullbackEndpointIso s).hom ≫ m.left := pullbackComparisonApp_snd m (Fin.last n)

end Pullback

section Pushout
variable [HasPushouts C]

def pushoutEndpointIso (s : InitialReplacement C n) : s.right ≅ (pushoutPath s).obj 0 := by
  have : IsIso (initialLeg s.left 0) := by
    rw [initialLeg_zero]
    infer_instance
  exact asIso (pushout.inl s.hom (initialLeg s.left 0))

lemma pushoutEndpointIso_fac (s : InitialReplacement C n) :
    s.hom ≫ (pushoutEndpointIso s).hom = (pushoutInclusion s).app 0 := by
  calc
    _ = initialLeg s.left 0 ≫ pushout.inr s.hom (initialLeg s.left 0) := pushout.condition
    _ = 𝟙 _ ≫ pushout.inr s.hom (initialLeg s.left 0) :=
      congrArg (fun g => g ≫ pushout.inr s.hom (initialLeg s.left 0)) (initialLeg_zero s.left)
    _ = _ := Category.id_comp _

lemma pushoutEndpointIso_naturality {s t : InitialReplacement C n} (m : s ⟶ t) :
    m.right ≫ (pushoutEndpointIso t).hom =
      (pushoutEndpointIso s).hom ≫ (pushoutComparison m).app 0 :=
  (pushoutComparisonApp_inl m 0).symm

end Pushout
end SerrePositivity.EInfinity.Hammock.ForwardPath
