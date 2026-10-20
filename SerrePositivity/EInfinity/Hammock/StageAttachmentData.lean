module

public import SerrePositivity.EInfinity.Hammock.LengthBoundaryLift
public import SerrePositivity.EInfinity.Hammock.WordMaximal
public import SerrePositivity.EInfinity.Hammock.WordTopStage
public import SerrePositivity.EInfinity.Hammock.WordImageFactorization

/-!
# 元の境界上で整合する貼り合わせデータ

概要：前段階からの射と最大交互語からの射が境界で整合するデータをまとめる。
方針：短い語には前段階、最大語には指定された射を使い、全写像への整合を証明する。
規約：最大語の型は元の語を保持する部分型。境界は元の像の和。
使われ方：段階の pushout の普遍性。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

structure StageAttachmentData {F : Word ⥤ SSet.{w}} (hF : ProperDiagram F) (n : ℕ)
    (Z : SSet.{w}) where
  lower : lengthStage F n ⟶ Z
  upper : ∀ a : Word.MaximalAlternating n, F.obj a.val ⟶ Z
  boundary : ∀ a : Word.MaximalAlternating n,
    lengthBoundaryToStage hF n a.val ≫ lower = (lengthBoundary F n a.val).ι ≫ upper a

variable {F : Word ⥤ SSet.{w}} {hF : ProperDiagram F} {n : ℕ} {Z : SSet.{w}}
  (d : StageAttachmentData hF n Z)

def stageAttachmentComponent (a : Word.TopStage (n + 1)) : F.obj a.obj.obj ⟶ Z :=
  if h : a.obj.obj.length ≤ n then lengthStageInclusion F n a.obj.obj h ≫ d.lower
  else d.upper ⟨a.obj.obj, Nat.le_antisymm a.obj.property (by omega),
    a.property.resolve_left (fun hs => h (Nat.lt_succ_iff.mp hs))⟩

lemma stageAttachmentComponent_short (a : Word.TopStage (n + 1)) (ha : a.obj.obj.length ≤ n) :
    stageAttachmentComponent d a = lengthStageInclusion F n a.obj.obj ha ≫ d.lower :=
  dite_eq_left ha

lemma stageAttachmentComponent_top (a : Word.TopStage (n + 1))
    (ha : a.obj.obj.length = n + 1) (ha' : Word.IsAlternating a.obj.obj) :
    stageAttachmentComponent d a = d.upper ⟨a.obj.obj, ha, ha'⟩ := by
  rw [stageAttachmentComponent, dite_eq_right (by omega)]

lemma stageAttachmentComponent_naturality {a b : Word.TopStage (n + 1)} (f : a ⟶ b) :
    F.map f.hom.hom ≫ stageAttachmentComponent d b = stageAttachmentComponent d a := by
  by_cases ha : a.obj.obj.length ≤ n
  · by_cases hb : b.obj.obj.length ≤ n
    · rw [stageAttachmentComponent_short d a ha, stageAttachmentComponent_short d b hb,
        ← Category.assoc, lengthStageInclusion_naturality]
    · have hbLen : b.obj.obj.length = n + 1 := Nat.le_antisymm b.obj.property (by omega)
      have hbAlt : Word.IsAlternating b.obj.obj :=
        b.property.resolve_left (fun hs => hb (Nat.lt_succ_iff.mp hs))
      let B : Word.MaximalAlternating n := ⟨b.obj.obj, hbLen, hbAlt⟩
      let g := f.hom.hom
      have hq : (Word.imageWord g).length ≤ n := (Word.imageWord_length_le g).trans ha
      have hi : F.map (Word.imageInclusion g) ≫ d.upper B =
          lengthStageInclusion F n (Word.imageWord g) hq ≫ d.lower := by
        have he := congrArg (fun η => lengthBoundaryLift F n hq (Word.imageInclusion g)
          (Word.imageInclusion_injective g) ≫ η) (d.boundary B)
        rw [← Category.assoc, lengthBoundaryLift_toStage, ← Category.assoc,
          lengthBoundaryLift_ι] at he
        exact he.symm
      rw [stageAttachmentComponent_short d a ha, stageAttachmentComponent_top d b hbLen hbAlt]
      change F.map g ≫ d.upper B = _
      rw [← Word.toImage_fac g, CategoryTheory.Functor.map_comp, Category.assoc, hi,
        ← Category.assoc, lengthStageInclusion_naturality]
  · have haLen : a.obj.obj.length = n + 1 := Nat.le_antisymm a.obj.property (by omega)
    have haAlt : Word.IsAlternating a.obj.obj :=
      a.property.resolve_left (fun hs => ha (Nat.lt_succ_iff.mp hs))
    obtain ⟨hw, hf⟩ := haAlt.target_eq_of_length_le f.hom.hom (by
      have hb := b.obj.property
      change b.obj.obj.length ≤ n + 1 at hb
      omega)
    have hab : a = b := by
      apply ObjectProperty.FullSubcategory.ext
      apply ObjectProperty.FullSubcategory.ext
      exact hw
    subst b
    have hf' : f = 𝟙 a := by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      change f.hom.hom = 𝟙 a.obj.obj
      simpa only [eqToHom_refl] using hf
    subst f
    change F.map (𝟙 a.obj.obj) ≫ stageAttachmentComponent d a = stageAttachmentComponent d a
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.EInfinity.Hammock
