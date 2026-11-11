module
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy

/-!
概要：指定した四辺・四頂点経路の全比較を同じ後合成で写す。
方針：元四ホモトピーと共有経路式を全単体で後合成する。
規約：元比較を選び直さない。使われ方：Cat^perf の実境界を同じ StableInfinity へ忘れる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：元全ホモトピーの同じ後合成。
方針：元全写像と元二端点を写す。規約：同じ時刻パラメータ。
使われ方：指定四境界の同時後合成。 -/
def specifiedHomotopyPostcomp {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (k : X ⟶ Y) : SSet.Homotopy (f ≫ k) (g ≫ k) where
  h := H.h ≫ k
  h₀ := by rw [← Category.assoc, H.h₀]; rfl
  h₁ := by rw [← Category.assoc, H.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元四境界の全比較は同じ後合成で元共有経路と可逆性を保つ。
方針：元四比較と元四接合式を同時に写す。
規約：元全側面を保持。使われ方：実 Cat^perf 境界の StableInfinity 比較。 -/
def squareFrameHomotopyPostcomp {X Y : SSet.{u}}
    {f g : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g)) (k : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (f ≫ k)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (g ≫ k)) where
  bottom := specifiedHomotopyPostcomp H.bottom k
  right := specifiedHomotopyPostcomp H.right k
  left := specifiedHomotopyPostcomp H.left k
  top := specifiedHomotopyPostcomp H.top k
  lower_left := by simpa only [specifiedHomotopyPostcomp, Category.assoc] using congrArg (fun p => p ≫ k) H.lower_left
  lower_right := by simpa only [specifiedHomotopyPostcomp, Category.assoc] using congrArg (fun p => p ≫ k) H.lower_right
  upper_left := by simpa only [specifiedHomotopyPostcomp, Category.assoc] using congrArg (fun p => p ≫ k) H.upper_left
  upper_right := by simpa only [specifiedHomotopyPostcomp, Category.assoc] using congrArg (fun p => p ≫ k) H.upper_right
  bottom_invertible := fun x => (H.bottom_invertible x).map k
  right_invertible := fun x => (H.right_invertible x).map k
  left_invertible := fun x => (H.left_invertible x).map k
  top_invertible := fun x => (H.top_invertible x).map k
end SerrePositivity.KST.SConstruction
