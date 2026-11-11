module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionGeneratorHomOperators

/-!
# 元の自由 Hom の一文字の列による追加退化

概要：元の射を一文字の列へ送り、同じ Hom の次数を一つ上げる。
方針：標準生成対象の再帰表示で元の Quiver.Hom.toPath をそのまま使う。
規約：恒等射も一文字として保持し、圏の関手だとは仮定しない。
使われ方：元の Hom augmentation の実際の収縮。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
open scoped Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

def generatorHomSection (f : X ⟶ Y) : (freeResolutionGeneratorHom C X Y) _⦋0⦌ :=
  Quiver.Hom.toPath (V := C.category) f

def generatorHomExtra (n : ℕ) (f : (freeResolutionGeneratorHom C X Y) _⦋n⦌) :
    (freeResolutionGeneratorHom C X Y) _⦋n + 1⦌ :=
  Quiver.Hom.toPath (V := (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).category) f

lemma generatorHomSection_augmentation (f : X ⟶ Y) :
    (freeResolutionGeneratorHomAugmentation C X Y).app (op ⦋0⦌) (generatorHomSection C f) = f := by
  apply eq_of_heq
  exact (generatorHom_augmentation_heq C 0 (generatorHomSection C f)).trans
    (heq_of_eq (composePath_toPath f))

lemma generatorHomExtra_face_zero (n : ℕ) (f : (freeResolutionGeneratorHom C X Y) _⦋n⦌) :
    (freeResolutionGeneratorHom C X Y).δ (0 : Fin (n + 2)) (generatorHomExtra C n f) = f := by
  apply eq_of_heq
  have hh := generatorHom_face_heq C n (0 : Fin (n + 2)) (generatorHomExtra C n f)
  rw [face_zero] at hh
  exact hh.trans (heq_of_eq (composePath_toPath f))

end SerrePositivity.EInfinity.SimplicialLocalization
