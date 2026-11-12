module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# 全列が指定である元の zigzag の指定部分圏への回収

概要：全列が W に属する元の図式を、指定部分圏の全射を許す zigzag 図式に移す。
方針：元の各射と全縦射の所属証明を、そのまま指定部分圏の射にする。
規約：元の包含へ戻すと同じ全対象・全射の関手を厳密に回収する。
使われ方：指定 prefix の実際の W-hammock の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def inclusion : LocalizerMorphism (⊤ : MorphismProperty (WideSubcategory W)) W where
  functor := wideSubcategoryInclusion W
  map _ _ f _ := f.property

def obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (hS : ∀ j, W (S.arrow j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w ⟨X⟩ ⟨Y⟩ where
  vertex j := ⟨S.vertex j⟩
  first := congrArg (fun Z : C => (⟨Z⟩ : WideSubcategory W)) S.first
  last := congrArg (fun Z : C => (⟨Z⟩ : WideSubcategory W)) S.last
  arrow j := ⟨S.arrow j, hS j⟩
  backward_mem _ _ := trivial

lemma wide_eqToHom {P Q : WideSubcategory W} (h : P = Q) :
    (eqToHom h).hom = eqToHom (congrArg WideSubcategory.obj h) := by cases h; rfl

def map {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (hS : ∀ j, W (S.arrow j)) (hT : ∀ j, W (T.arrow j))
    (f : S ⟶ T) : obj W S hS ⟶ obj W T hT where
  app j := ⟨f.app j, f.app_mem j⟩
  app_mem _ := trivial
  first := by
    apply WideSubcategory.hom_ext
    rw [wide_eqToHom]
    exact f.first
  last := by
    apply WideSubcategory.hom_ext
    rw [wide_eqToHom]
    exact f.last
  comm j := by
    apply WideSubcategory.hom_ext
    exact f.comm j

variable {D : Type uD} [Category.{vD} D]

def liftFunctor (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (hF : ∀ d j, W ((F.obj d).arrow j)) :
    D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w ⟨X⟩ ⟨Y⟩ where
  obj d := obj W (F.obj d) (hF d)
  map f := map W (hF _) (hF _) (F.map f)
  map_id d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.app j) (F.map_id d)
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.app j) (F.map_comp f g)

lemma liftFunctor_inclusion (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (hF : ∀ d j, W ((F.obj d).arrow j)) :
    liftFunctor W F hF ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (inclusion W) = F := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift
