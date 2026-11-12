module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallKanHomotopy
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallAction
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PresentationKernelQuotient

/-!
# 中断した任意モデル源への一般化：OrdinaryBarHomotopyDescent

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Strict descent on the original base with homotopy-class morphisms。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0197][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0197
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict descent on the original base with homotopy-class morphisms

The values are actual small Kan sets, but the arrows are homotopy classes.
This establishes ordinary categorical descent only. It does not supply a
strict SSet-valued bifunctor or any unproved higher coherence.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def functor : Cᵒᵖ × C ⥤ SmallKanHomotopy.Object.{v} where
  obj X := ⟨OrdinaryBarSmallReference.value hcof hfib X,
    OrdinaryBarSmallReference.value_kan hcof hfib X⟩
  map {X Y} f := by
    change HomotopyClasses.obj (OrdinaryBarSmallReference.value hcof hfib X)
      (OrdinaryBarSmallReference.value hcof hfib Y)
    exact HomotopyClasses.mk (OrdinaryBarSmallAction.arrow hcof hfib f)
  map_id X := by
    change HomotopyClasses.mk (OrdinaryBarSmallAction.arrow hcof hfib (𝟙 X)) =
      HomotopyClasses.mk (𝟙 (OrdinaryBarSmallReference.value hcof hfib X))
    exact HomotopyClasses.sound
      (Classical.choice (OrdinaryBarSmallAction.arrow_id_homotopy hcof hfib X))
  map_comp f g := by
    change HomotopyClasses.mk (OrdinaryBarSmallAction.arrow hcof hfib (f ≫ g)) =
      HomotopyClasses.mk (OrdinaryBarSmallAction.arrow hcof hfib f ≫
        OrdinaryBarSmallAction.arrow hcof hfib g)
    exact HomotopyClasses.sound
      (Classical.choice (OrdinaryBarSmallAction.arrow_comp_homotopy hcof hfib f g))

abbrev realization := SmallKanHomotopy.realization.{v, max u v}
  AnodyneHomotopy.anodyneQ.{max u v}

def realizationIso : functor (C := C) hcof hfib ⋙ realization.{v, u} ≅
    OrdinaryResolutionBar.functor ⋙ AnodyneHomotopy.anodyneQ :=
  NatIso.ofComponents (OrdinaryBarSmallReference.comparisonIso hcof hfib) (by
    intro X Y f
    change AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} (OrdinaryBarSmallAction.arrow hcof hfib f)) ≫
          (OrdinaryBarSmallReference.comparisonIso hcof hfib Y).hom = _
    rw [OrdinaryBarSmallAction.arrow_map]
    simp only [OrdinaryBarSmallAction.transported, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl)

include hcof hfib in
lemma map_isIso {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso ((functor hcof hfib).map f) := by
  let R := realization.{v, u}
  let hR := SmallKanHomotopy.fullyFaithful.{v, max u v} AnodyneHomotopy.anodyneQ
  let : R.Full := hR.full
  let : R.Faithful := hR.faithful
  have : IsIso (R.map ((functor hcof hfib).map f)) := by
    change IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} (OrdinaryBarSmallAction.arrow hcof hfib f)))
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.anodyneQ_map_isIso_of_weakEquivalence hcof hfib _
      (OrdinaryBarSmallAction.arrow_weakEquivalence hcof hfib f hs ht)
  exact isIso_of_reflects_iso _ R

def presentation : RightResolutionMapping.Index C ⥤ SmallKanHomotopy.Object.{v} where
  obj R := ⟨PresentationKernelQuotient.functor.obj R,
    PresentationKernelQuotient.terminal_rlp R⟩
  map f := HomotopyClasses.mk (PresentationKernelQuotient.functor.map f)
  map_id R := congrArg HomotopyClasses.mk (PresentationKernelQuotient.functor.map_id R)
  map_comp f g := congrArg HomotopyClasses.mk
    (PresentationKernelQuotient.functor.map_comp f g)

/-- This is descent in an ordinary homotopy category, not strict simplicial descent. -/
def presentationIso : RightResolutionMapping.projection ⋙ functor (C := C) hcof hfib ≅
    presentation (C := C) := by
  let R := realization.{v, u}
  let hR := SmallKanHomotopy.fullyFaithful.{v, max u v} AnodyneHomotopy.anodyneQ
  letI : R.Full := hR.full
  letI : R.Faithful := hR.faithful
  apply Functor.fullyFaithfulCancelRight R
  exact Functor.isoWhiskerLeft RightResolutionMapping.projection
      (realizationIso hcof hfib) ≪≫
    (PresentationKernelQuotient.baseComparisonIso hcof hfib
      AnodyneHomotopy.anodyneQ (Localization.inverts AnodyneHomotopy.anodyneQ _)).symm

include hcof hfib in
lemma presentation_map_eq_of_base_eq {X Y : RightResolutionMapping.Index C}
    (f g : X ⟶ Y) (h : RightResolutionMapping.projection.map f =
      RightResolutionMapping.projection.map g) :
    (presentation (C := C)).map f = (presentation (C := C)).map g := by
  let e := presentationIso (C := C) hcof hfib
  apply (cancel_epi (e.hom.app X)).mp
  rw [← e.hom.naturality f, ← e.hom.naturality g]
  change (functor hcof hfib).map (RightResolutionMapping.projection.map f) ≫ _ =
    (functor hcof hfib).map (RightResolutionMapping.projection.map g) ≫ _
  rw [h]

include hcof hfib in
lemma presentation_map_isIso_of_base_isIso {X Y : RightResolutionMapping.Index C}
    (f : X ⟶ Y) [IsIso (RightResolutionMapping.projection.map f)] :
    IsIso ((presentation (C := C)).map f) := by
  apply (NatIso.isIso_map_iff (presentationIso (C := C) hcof hfib) f).mp
  change IsIso ((functor hcof hfib).map (RightResolutionMapping.projection.map f))
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent
