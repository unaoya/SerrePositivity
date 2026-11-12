module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UniversalScaffoldEvaluation
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Comma

/-!
概要：余極限の各項上の整合する section の族を、全体上の元の図式へ貼り合わせる。
方針：各族を uncurry し、右直積による余極限の保存を使う。
規約：全パラメーターを保持し、底上の射と制限は厳密な等式で指定する。
使われ方：section とその core の厳密な降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 整合する section の族を展開し、元の全空間を頂点とする余錐を作る。 -/
def cocartesianSectionFamilyTensorCocone {J : Type v} [Category.{w} J]
    {T E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B)
    (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D.obj j).hom)
    (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f)) :
    Cocone (D ⋙ Over.forget B ⋙ tensorRight T) where
  pt := E
  ι :=
    { app j := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry (s j)
      naturality {j k} f := by
        change ((D.map f).left ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry (s k) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry (s j)
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsUncurry_overPre, ← hs f] }

/-- 底上の余極限をパラメーターと右直積しても、余極限の普遍性を保持する。 -/
def cocartesianSectionTensorCocone_isColimit {J : Type v} [Category.{w} J]
    {B T : SSet.{u}} {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c)) :
    IsColimit ((tensorRight T).mapCocone ((Over.forget B).mapCocone c)) :=
  isColimitOfPreserves (tensorRight T) hc

/-- 元の各 section の族を、余極限と全パラメーターの直積上の図式へ貼る。 -/
def cocartesianSectionFamilyColimitUncurry {J : Type v} [Category.{w} J]
    {T E B : SSet.{u}} (p : E ⟶ B) {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c))
    (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D.obj j).hom)
    (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f)) :
    c.pt.left ⊗ T ⟶ E :=
  (cocartesianSectionTensorCocone_isColimit c hc).desc
    (cocartesianSectionFamilyTensorCocone p D s hs)

/-- 貼り合わせた図式は、各項上の元の section の族を厳密に回収する。 -/
lemma cocartesianSectionFamilyColimitUncurry_fac {J : Type v} [Category.{w} J]
    {T E B : SSet.{u}} (p : E ⟶ B) {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c))
    (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D.obj j).hom)
    (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f)) (j : J) :
    ((c.ι.app j).left ▷ T) ≫ cocartesianSectionFamilyColimitUncurry p c hc s hs =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry (s j) :=
  (cocartesianSectionTensorCocone_isColimit c hc).fac _ j

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
