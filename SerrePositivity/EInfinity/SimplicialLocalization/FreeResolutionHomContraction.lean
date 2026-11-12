module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionHomExtraNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 元の自由解消 Hom augmentation の収縮

概要：元の圏の Hom へ向かう自由解消 augmentation は弱ホモトピー同値。
方針：一文字の追加退化の全恒等式から実際の区間収縮を構成する。
規約：単体集合のモデル構造と標的の Kan 性は仮定しない。
使われ方：DK ホモトピー補題2.4の底の Hom の入力。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite
open scoped Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionGeneratorHomAugmented : SimplicialObject.Augmented (Type u) :=
  { left := freeResolutionGeneratorHom C X Y
    right := X ⟶ Y
    hom := freeResolutionGeneratorHomAugmentation C X Y }

def freeResolutionGeneratorHomExtraDegeneracy :
    (freeResolutionGeneratorHomAugmented C X Y).ExtraDegeneracy where
  s' := ↾(generatorHomSection C)
  s n := ↾(generatorHomExtra C n)
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro f
    exact generatorHomSection_augmentation C f
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact generatorHomExtra_face_one C f
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro f
    exact generatorHomExtra_face_zero C n f
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    exact generatorHomExtra_face_succ C n i f
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    exact generatorHomExtra_degeneracy_succ C n i f

lemma freeResolutionGeneratorHomAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (freeResolutionGeneratorHomAugmentation C X Y) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.localized_augmentation_isIso
      (freeResolutionGeneratorHomExtraDegeneracy C X Y))

end SerrePositivity.EInfinity.SimplicialLocalization
