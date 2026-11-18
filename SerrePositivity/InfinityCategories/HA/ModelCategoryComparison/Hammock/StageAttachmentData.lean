module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundaryLift
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMaximal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordTopStage
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordImageFactorization

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

structure StageAttachmentData {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (n : ℕ)
    (Z : SSet.{w}) where
  lower : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F n ⟶ Z
  upper : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n, F.obj a.val ⟶ Z
  boundary : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryToStage hF n a.val ≫ lower = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n a.val).ι ≫ upper a

variable {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} {hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F} {n : ℕ} {Z : SSet.{w}}
  (d : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.StageAttachmentData hF n Z)

def stageAttachmentComponent (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1)) : F.obj a.obj.obj ⟶ Z :=
  if h : a.obj.obj.length ≤ n then _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj.obj h ≫ d.lower
  else d.upper ⟨a.obj.obj, Nat.le_antisymm a.obj.property (by omega),
    a.property.resolve_left (fun hs => h (Nat.lt_succ_iff.mp hs))⟩

lemma stageAttachmentComponent_short (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1)) (ha : a.obj.obj.length ≤ n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent d a = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj.obj ha ≫ d.lower :=
  dite_eq_left ha

lemma stageAttachmentComponent_top (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1))
    (ha : a.obj.obj.length = n + 1) (ha' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating a.obj.obj) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent d a = d.upper ⟨a.obj.obj, ha, ha'⟩ := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent, dite_eq_right (by omega)]

lemma stageAttachmentComponent_naturality {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage (n + 1)} (f : a ⟶ b) :
    F.map f.hom.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent d b = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent d a := by
  by_cases ha : a.obj.obj.length ≤ n
  · by_cases hb : b.obj.obj.length ≤ n
    · rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent_short d a ha, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent_short d b hb,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_naturality]
    · have hbLen : b.obj.obj.length = n + 1 := Nat.le_antisymm b.obj.property (by omega)
      have hbAlt : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating b.obj.obj :=
        b.property.resolve_left (fun hs => hb (Nat.lt_succ_iff.mp hs))
      let B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n := ⟨b.obj.obj, hbLen, hbAlt⟩
      let g := f.hom.hom
      have hq : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageWord g).length ≤ n := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageWord_length_le g).trans ha
      have hi : F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion g) ≫ d.upper B =
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageWord g) hq ≫ d.lower := by
        have he := congrArg (fun η => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift F n hq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion g)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion_injective g) ≫ η) (d.boundary B)
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift_toStage, ← Category.assoc,
          _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift_ι] at he
        exact he.symm
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent_short d a ha, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent_top d b hbLen hbAlt]
      change F.map g ≫ d.upper B = _
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toImage_fac g, CategoryTheory.Functor.map_comp, Category.assoc, hi,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_naturality]
  · have haLen : a.obj.obj.length = n + 1 := Nat.le_antisymm a.obj.property (by omega)
    have haAlt : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating a.obj.obj :=
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
    change F.map (𝟙 a.obj.obj) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent d a = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageAttachmentComponent d a
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
