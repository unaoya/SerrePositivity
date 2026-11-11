module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexShapeFamilyPushout
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：添字を保つ依存和による任意の余極限の保存。
方針：各係数の普遍射を依存和にまとめ、各添字で一意性を検査する。
規約：図式の射に単射性を仮定しない。
使われ方：単体圏の nerve の小余積・transfinite な付加への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w w'
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 固定した添字ごとの型の図式を、依存和全体の図式へまとめる。 -/
def simplexShapeFamilyDiagram {I : Type v} {J : Type w} [Category.{w'} J]
    (F : I → J ⥤ Type (max u v)) : J ⥤ Type (max u v) where
  obj j := Σ i, (F i).obj j
  map f := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyMap.{u, v} (fun i ↦ (F i).map f)
  map_id j := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((F i).map_id j) x)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((F i).map_comp f g) x)

/-- 各係数の cocone を、依存和全体の cocone にまとめる。 -/
def simplexShapeFamilyCocone {I : Type v} {J : Type w} [Category.{w'} J]
    {F : I → J ⥤ Type (max u v)} (c : ∀ i, Cocone (F i)) :
    Cocone (simplexShapeFamilyDiagram F) where
  pt := Σ i, (c i).pt
  ι := {
    app := fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyMap.{u, v} (fun i ↦ (c i).ι.app j)
    naturality := by
      intro j k f
      apply ConcreteCategory.hom_ext
      rintro ⟨i, x⟩
      exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((c i).ι.naturality f) x) }

/-- 依存和の図式の cocone を、一つの固定した添字へ制限する。 -/
def simplexShapeFamilyComponentCocone {I : Type v} {J : Type w} [Category.{w'} J]
    {F : I → J ⥤ Type (max u v)} (s : Cocone (simplexShapeFamilyDiagram F)) (i : I) :
    Cocone (F i) where
  pt := s.pt
  ι := {
    app := fun j ↦ ↾fun x ↦ s.ι.app j ⟨i, x⟩
    naturality := by
      intro j k f
      ext x
      exact ConcreteCategory.congr_hom (s.ι.naturality f) ⟨i, x⟩ }

/-- 各添字で余極限である cocone は、依存和全体でも余極限。 -/
def simplexShapeFamilyCoconeIsColimit {I : Type v} {J : Type w} [Category.{w'} J]
    {F : I → J ⥤ Type (max u v)} {c : ∀ i, Cocone (F i)}
    (hc : ∀ i, IsColimit (c i)) : IsColimit (simplexShapeFamilyCocone c) where
  desc s := ↾fun x ↦ (hc x.1).desc (simplexShapeFamilyComponentCocone s x.1) x.2
  fac s j := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact ConcreteCategory.congr_hom ((hc i).fac (simplexShapeFamilyComponentCocone s i) j) x
  uniq s m hm := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    have he : (↾fun y : (c i).pt ↦ m ⟨i, y⟩) =
        (hc i).desc (simplexShapeFamilyComponentCocone s i) := by
      apply (hc i).hom_ext
      intro j
      ext y
      exact (ConcreteCategory.congr_hom (hm j) ⟨i, y⟩).trans
        (ConcreteCategory.congr_hom
          ((hc i).fac (simplexShapeFamilyComponentCocone s i) j) y).symm
    exact ConcreteCategory.congr_hom he x

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
