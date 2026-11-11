module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionMarkedHom

/-!
# 元の指定 Hom augmentation の収縮

概要：指定射の自由解消から元の指定 Hom への augmentation は弱ホモトピー同値。
方針：元の一文字の追加退化を指定射の部分単体集合へ制限する。
規約：元の全単体作用素と指定射の類を保持する。
使われ方：DK ホモトピー補題2.4の二つ目の入力。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionMarkedHomAugmented : SimplicialObject.Augmented (Type u) :=
  { left := freeResolutionMarkedHom C X Y
    right := {f : X ⟶ Y // C.weakEquivalences f}
    hom := freeResolutionMarkedHomAugmentation C X Y }

def freeResolutionMarkedHomExtraDegeneracy :
    (freeResolutionMarkedHomAugmented C X Y).ExtraDegeneracy where
  s' := ↾(freeResolutionMarkedHomSection C X Y)
  s n := ↾(freeResolutionMarkedHomExtra C X Y n)
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact generatorHomSection_augmentation C f.val
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact generatorHomExtra_face_one C f.val
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact generatorHomExtra_face_zero C n f.val
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact generatorHomExtra_face_succ C n i f.val
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact generatorHomExtra_degeneracy_succ C n i f.val

lemma freeResolutionMarkedHomAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (freeResolutionMarkedHomAugmentation C X Y) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.localized_augmentation_isIso
      (freeResolutionMarkedHomExtraDegeneracy C X Y))

end SerrePositivity.EInfinity.SimplicialLocalization
