module

public import SerrePositivity.EInfinity.Hammock.StageAttachmentData
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TopStageColimit

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

variable {F : Word ⥤ SSet.{w}} {hF : ProperDiagram F} {n : ℕ} {Z : SSet.{w}}
  (d : StageAttachmentData hF n Z)

def stageAttachmentCocone : Cocone (topStageDiagram F (n + 1)) where
  pt := Z
  ι :=
    { app a := stageAttachmentComponent d a
      naturality a b f := by
        change F.map f.hom.hom ≫ stageAttachmentComponent d b =
          stageAttachmentComponent d a ≫ 𝟙 _
        rw [Category.comp_id]
        exact stageAttachmentComponent_naturality d f }

lemma topStageColimitIso_inv_fac (a : Word.TopStage (n + 1)) :
    lengthStageInclusion F (n + 1) a.obj.obj a.obj.property ≫
        (topStageColimitIso F (n + 1)).inv = colimit.ι (topStageDiagram F (n + 1)) a := by
  let := Word.topStageFinal (n + 1)
  exact Functor.Final.ι_colimitIso_inv (Word.topStageInclusion (n + 1))
    (Word.lengthInclusion (n + 1) ⋙ F) a

def stageAttachmentDesc : lengthStage F (n + 1) ⟶ Z :=
  (topStageColimitIso F (n + 1)).inv ≫
    colimit.desc (topStageDiagram F (n + 1)) (stageAttachmentCocone d)

lemma stageAttachmentDesc_fac (a : Word.TopStage (n + 1)) :
    lengthStageInclusion F (n + 1) a.obj.obj a.obj.property ≫ stageAttachmentDesc d =
      stageAttachmentComponent d a := by
  rw [stageAttachmentDesc, ← Category.assoc, topStageColimitIso_inv_fac, colimit.ι_desc]
  rfl

lemma stageAttachmentDesc_lower :
    lengthStageTransition F (Nat.le_succ n) ≫ stageAttachmentDesc d = d.lower := by
  apply colimit.hom_ext (F := Word.lengthInclusion n ⋙ F)
  intro a
  let A : Word.TopStage (n + 1) :=
    ⟨⟨a.obj, a.property.trans (Nat.le_succ n)⟩, Or.inl (Nat.lt_succ_of_le a.property)⟩
  change lengthStageInclusion F n a.obj a.property ≫
    (lengthStageTransition F (Nat.le_succ n) ≫ stageAttachmentDesc d) =
      lengthStageInclusion F n a.obj a.property ≫ d.lower
  rw [← Category.assoc, lengthStageInclusion_transition]
  exact (stageAttachmentDesc_fac d A).trans (stageAttachmentComponent_short d A a.property)

lemma stageAttachmentDesc_upper (a : Word.MaximalAlternating n) :
    lengthStageInclusion F (n + 1) a.val a.property.1.le ≫ stageAttachmentDesc d = d.upper a := by
  let A : Word.TopStage (n + 1) := ⟨⟨a.val, a.property.1.le⟩, Or.inr a.property.2⟩
  exact (stageAttachmentDesc_fac d A).trans
    (stageAttachmentComponent_top d A a.property.1 a.property.2)

lemma stageAttachmentDesc_unique (f : lengthStage F (n + 1) ⟶ Z)
    (hl : lengthStageTransition F (Nat.le_succ n) ≫ f = d.lower)
    (hu : ∀ a : Word.MaximalAlternating n,
      lengthStageInclusion F (n + 1) a.val a.property.1.le ≫ f = d.upper a) :
    f = stageAttachmentDesc d := by
  apply (cancel_epi (topStageColimitIso F (n + 1)).hom).1
  apply colimit.hom_ext (F := topStageDiagram F (n + 1))
  intro a
  rw [← Category.assoc, topStageColimitIso_fac]
  rw [← Category.assoc, topStageColimitIso_fac, stageAttachmentDesc_fac]
  by_cases ha : a.obj.obj.length ≤ n
  · rw [stageAttachmentComponent_short d a ha]
    rw [← hl, ← Category.assoc, lengthStageInclusion_transition]
  · have haLen : a.obj.obj.length = n + 1 := Nat.le_antisymm a.obj.property (by omega)
    have haAlt : Word.IsAlternating a.obj.obj :=
      a.property.resolve_left (fun hs => ha (Nat.lt_succ_iff.mp hs))
    rw [stageAttachmentComponent_top d a haLen haAlt]
    exact hu ⟨a.obj.obj, haLen, haAlt⟩

end SerrePositivity.EInfinity.Hammock
