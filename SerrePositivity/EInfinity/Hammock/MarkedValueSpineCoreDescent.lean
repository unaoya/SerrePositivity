module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineGenerators
public import Mathlib.CategoryTheory.Core

/-!
# 指定矢を反転する元の関手の指定自由 groupoid からの延長

概要：元の反転関手の指定生成矢を Core の同型として送り、自由 groupoid に延長する。
方針：元の IsInvertedBy と FreeGroupoid.lift の普遍性を使う。
規約：指定生成矢の元の像と元の全対象を回収する。
使われ方：値の因子列の圏の局所化の普遍性。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [Category.{vD} D] (F : Paths C ⥤ D) (hF : W.paths.IsInvertedBy F)

def markedCorePrefunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W ⥤q Core D where
  obj X := ⟨F.obj X⟩
  map f := by
    have := hF f.val.toPath (MorphismProperty.toPath_mem_paths f.property)
    exact ⟨asIso (F.map f.val.toPath)⟩

def markedValueDescent : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⥤ D :=
  Quiver.FreeGroupoid.lift (markedCorePrefunctor W F hF) ⋙ Core.inclusion D

lemma markedValueDescent_generator {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W} (f : X ⟶ Y) :
    (markedValueDescent W F hF).map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map f) =
      F.map f.val.toPath := by
  have he := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (markedCorePrefunctor W F hF)) f
  have hh : (Quiver.FreeGroupoid.lift (markedCorePrefunctor W F hF)).map
      ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map f) =
        (markedCorePrefunctor W F hF).map f := by
    simpa only [Quiver.homOfEq_rfl, Prefunctor.comp_map, Functor.toPrefunctor_map] using he
  exact congrArg (fun p => p.iso.hom) hh

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
