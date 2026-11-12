module

public import SerrePositivity.EInfinity.Hammock.StageAttachmentData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStageColimit

/-!
# 境界で整合するデータから元の次段階への一意な射

概要：前段階と最大交互語の射が境界で整合すれば、次段階から一意に延長できる。
方針：元の TopStage の余錐を作り、同じ包含による余極限の同型を用いる。
規約：元の標準射上の計算式と一意性を保持する。
使われ方：元の段階の pushout の普遍性。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} {hF : ProperDiagram F} {n : ℕ} {Z : SSet.{w}}
  (d : StageAttachmentData hF n Z)

def stageAttachmentCocone : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageDiagram F (n + 1)) where
  pt := Z
  ι :=
    { app a := stageAttachmentComponent d a
      naturality a b f := by
        change F.map f.hom.hom ≫ stageAttachmentComponent d b =
          stageAttachmentComponent d a ≫ 𝟙 _
        rw [Category.comp_id]
        exact stageAttachmentComponent_naturality d f }

lemma topStageColimitIso_inv_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F (n + 1) a.obj.obj a.obj.property ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso F (n + 1)).inv = colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageDiagram F (n + 1)) a := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageFinal (n + 1)
  exact Functor.Final.ι_colimitIso_inv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageInclusion (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion (n + 1) ⋙ F) a

def stageAttachmentDesc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F (n + 1) ⟶ Z :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso F (n + 1)).inv ≫
    colimit.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageDiagram F (n + 1)) (stageAttachmentCocone d)

lemma stageAttachmentDesc_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F (n + 1) a.obj.obj a.obj.property ≫ stageAttachmentDesc d =
      stageAttachmentComponent d a := by
  rw [stageAttachmentDesc, ← Category.assoc, topStageColimitIso_inv_fac, colimit.ι_desc]
  rfl

lemma stageAttachmentDesc_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F (Nat.le_succ n) ≫ stageAttachmentDesc d = d.lower := by
  apply colimit.hom_ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F)
  intro a
  let A : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1) :=
    ⟨⟨a.obj, a.property.trans (Nat.le_succ n)⟩, Or.inl (Nat.lt_succ_of_le a.property)⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F (Nat.le_succ n) ≫ stageAttachmentDesc d) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫ d.lower
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_transition]
  exact (stageAttachmentDesc_fac d A).trans (stageAttachmentComponent_short d A a.property)

lemma stageAttachmentDesc_upper (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F (n + 1) a.val a.property.1.le ≫ stageAttachmentDesc d = d.upper a := by
  let A : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1) := ⟨⟨a.val, a.property.1.le⟩, Or.inr a.property.2⟩
  exact (stageAttachmentDesc_fac d A).trans
    (stageAttachmentComponent_top d A a.property.1 a.property.2)

lemma stageAttachmentDesc_unique (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F (n + 1) ⟶ Z)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F (Nat.le_succ n) ≫ f = d.lower)
    (hu : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F (n + 1) a.val a.property.1.le ≫ f = d.upper a) :
    f = stageAttachmentDesc d := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso F (n + 1)).hom).1
  apply colimit.hom_ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageDiagram F (n + 1))
  intro a
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso_fac]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso_fac, stageAttachmentDesc_fac]
  by_cases ha : a.obj.obj.length ≤ n
  · rw [stageAttachmentComponent_short d a ha]
    rw [← hl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_transition]
  · have haLen : a.obj.obj.length = n + 1 := Nat.le_antisymm a.obj.property (by omega)
    have haAlt : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating a.obj.obj :=
      a.property.resolve_left (fun hs => ha (Nat.lt_succ_iff.mp hs))
    rw [stageAttachmentComponent_top d a haLen haAlt]
    exact hu ⟨a.obj.obj, haLen, haAlt⟩

end SerrePositivity.EInfinity.Hammock
