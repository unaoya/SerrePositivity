module

public import SerrePositivity.KST.LocalizingInvariants.ProFullyFaithfulReflection
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
概要：元の塔を対象の性質で定まる充満部分圏へ持ち上げ、元の実 pro 逆を反映する。
方針：同じ対象・遷移・射を使い、充満忠実な包含で逆の二つの三角形を反映する。
規約：新たな逆の存在は入力しない。使われ方：有界 dg 模型の class 関手への移送。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  (X : Tower C) (hX : ∀ i, P (X.obj i))

def fullSubcategoryTower : Tower P.FullSubcategory where
  obj i := ⟨X.obj i, hX i⟩
  transition h := ObjectProperty.homMk (X.transition h)
  transition_self i := by
    apply ObjectProperty.hom_ext
    exact X.transition_self i
  transition_comp hm hn := by
    apply ObjectProperty.hom_ext
    exact X.transition_comp hm hn

variable {X} {Y : Tower C} (f : LevelHom X Y) (hY : ∀ i, P (Y.obj i))

def fullSubcategoryLevelHom :
    LevelHom (fullSubcategoryTower P X hX) (fullSubcategoryTower P Y hY) where
  app i := ObjectProperty.homMk (f.app i)
  naturality h := by
    apply ObjectProperty.hom_ext
    exact f.naturality h

lemma fullSubcategoryLevelHom_isProIso (hf : IsProIso f) :
    IsProIso (fullSubcategoryLevelHom P hX f hY) :=
  proIso_of_fullyFaithful P.ι (fullSubcategoryLevelHom P hX f hY) hf

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
