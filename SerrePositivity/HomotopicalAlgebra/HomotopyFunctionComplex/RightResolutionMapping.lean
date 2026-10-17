module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalQuillen
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanReplacement

/-!
# 中断した任意モデル源への一般化：RightResolutionMapping

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Simultaneous source and target resolution mapping spaces。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0331][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0331
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simultaneous source and target resolution mapping spaces

All values and the diagonal comparison are in the original Hom universe.
The index retains actual source frame maps and dual target frame maps.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.RightResolutionMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev Index (C : Type u) [Category.{v} C] [ModelCategory C] :=
  (FramedResolution C)ᵒᵖ × DualResolutionTargets.FramedIndex C

def presentationRows : SimplexCategoryᵒᵖ ⥤ Index C ⥤ ReplacementMapping.Index C where
  obj n := (𝟭 (FramedResolution C)ᵒᵖ).prod (DualResolutionTargets.framedPresentation C n)
  map f := NatTrans.prod (𝟙 _) (Functor.whiskerLeft (DualResolutionTargets.framedForget C)
    ((DualResolutionTargets.presentations C).map f))
  map_id _ := by
    apply NatTrans.ext
    funext X
    apply Prod.ext
    · rfl
    · exact congr_app ((DualResolutionTargets.presentations C).map_id _) _
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply Prod.ext
    · exact (Category.id_comp _).symm
    · exact congr_app ((DualResolutionTargets.presentations C).map_comp f g) _

abbrev projection : Index C ⥤ Cᵒᵖ × C :=
  FramedResolution.projection.op.prod (DualResolutionTargets.framedBase C)

lemma presentation_projection (n : SimplexCategoryᵒᵖ) :
    (presentationRows (C := C)).obj n ⋙ ReplacementMapping.projection = projection := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev rows : SimplexCategoryᵒᵖ ⥤ Index C ⥤ SSet.{v} :=
  presentationRows ⋙
    (Functor.whiskeringRight (Index C) (ReplacementMapping.Index C) SSet.{v}).obj
      (ReplacementMapping.uncurried hcof hfib)

abbrev functor : Index C ⥤ SSet.{v} := (rows hcof hfib).flip ⋙ BisimplicialModel.diagonal
abbrev zero : Index C ⥤ SSet.{v} := (rows hcof hfib).obj (op (SimplexCategory.mk 0))

def degeneracy : (Functor.const SimplexCategoryᵒᵖ).obj (zero (C := C) hcof hfib) ⟶
    rows hcof hfib where
  app n := (rows hcof hfib).map (SimplexCategory.isTerminalZero.from n.unop).op
  naturality {n m} f := by
    change (𝟙 _) ≫ _ = _ ≫ _
    rw [Category.id_comp, ← (rows hcof hfib).map_comp]
    congr 1

def constantRowsIso :
    ((Functor.const SimplexCategoryᵒᵖ).obj (zero (C := C) hcof hfib)).flip ⋙
      BisimplicialModel.diagonal ≅ zero hcof hfib :=
  NatIso.ofComponents (fun X => DiagonalFrame.constantIso ((zero hcof hfib).obj X)) (by
    intro X Y f
    ext n x
    rfl)

/-- A natural comparison of the whole two-variable presentation diagram. -/
def comparison : zero (C := C) hcof hfib ⟶ functor hcof hfib :=
  (constantRowsIso hcof hfib).inv ≫ Functor.whiskerRight
    ((CategoryTheory.flipFunctor SimplexCategoryᵒᵖ (Index C) SSet.{v}).map
      (degeneracy hcof hfib)) BisimplicialModel.diagonal

lemma row_operator_weakEquivalence {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (X : Index C) :
    weakEquivalences SSet.{v} (((rows hcof hfib).map f).app X) :=
  ReplacementMapping.uncurried_weakEquivalence hcof hfib _
    ((weakEquivalences C).id_mem _) ((weakEquivalences C).id_mem _)

lemma comparison_weakEquivalence (X : Index C) :
    weakEquivalences SSet.{v} ((comparison hcof hfib).app X) := by
  apply (weakEquivalences SSet.{v}).comp_mem
  · exact (weakEquivalences SSet.{v}).of_isIso _
  · apply BisimplicialModel.diagonal_map_weakEquivalence hcof hfib
    intro n
    exact row_operator_weakEquivalence hcof hfib
      (SimplexCategory.isTerminalZero.from n.unop).op X

lemma map_weakEquivalence {X Y : Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((functor hcof hfib).map f) := by
  apply BisimplicialModel.diagonal_map_weakEquivalence hcof hfib
  intro n
  exact ReplacementMapping.uncurried_weakEquivalence hcof hfib _ hs ht

abbrev kanFunctor : Index C ⥤ SSet.{v} :=
  functor hcof hfib ⋙ SimplicialModel.KanReplacement.functor hcof hfib

def kanComparison : zero (C := C) hcof hfib ⟶ kanFunctor hcof hfib :=
  comparison hcof hfib ≫ Functor.whiskerLeft (functor hcof hfib)
    (SimplicialModel.KanReplacement.unit hcof hfib)

lemma kanComparison_weakEquivalence (X : Index C) :
    weakEquivalences SSet.{v} ((kanComparison hcof hfib).app X) :=
  (weakEquivalences SSet.{v}).comp_mem _ _ (comparison_weakEquivalence hcof hfib X)
    (SimplicialModel.KanReplacement.unit_weakEquivalence hcof hfib _)

lemma kanComplex (X : Index C) : SSet.KanComplex ((kanFunctor hcof hfib).obj X) :=
  SimplicialModel.KanReplacement.kanComplex hcof hfib _

lemma kanFunctor_map_weakEquivalence {X Y : Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((kanFunctor hcof hfib).map f) :=
  SimplicialModel.KanReplacement.map_weakEquivalence hcof hfib _
    (map_weakEquivalence hcof hfib f hs ht)

lemma kanComparison_piZero_bijective (X : Index C) :
    Function.Bijective (SSet.mapπ₀ ((kanComparison hcof hfib).app X)) := by
  have : SSet.KanComplex ((zero hcof hfib).obj X) :=
    ReplacementMapping.kanComplex hcof hfib X.1
      ((DualResolutionTargets.framedPresentation C (op (SimplexCategory.mk 0))).obj X.2)
  have : IsFibrant ((zero hcof hfib).obj X) :=
    SimplicialModel.KanReplacement.isFibrant_of_kanComplex hfib _
  have : IsFibrant ((kanFunctor hcof hfib).obj X) :=
    SimplicialModel.KanReplacement.isFibrant hcof hfib _
  have : WeakEquivalence ((kanComparison hcof hfib).app X) :=
    ⟨kanComparison_weakEquivalence hcof hfib X⟩
  exact SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof _

def piZeroEquiv {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : Index C) :
    SSet.π₀ ((kanFunctor hcof hfib).obj X) ≃
      (Q.obj ((projection (C := C)).obj X).1.unop ⟶
        Q.obj ((projection (C := C)).obj X).2) :=
  (Equiv.ofBijective _ (kanComparison_piZero_bijective hcof hfib X)).symm.trans
    (ReplacementMapping.piZeroEquiv hcof hfib Q X.1
      ((DualResolutionTargets.framedPresentation C (op (SimplexCategory.mk 0))).obj X.2))

end SerrePositivity.HomotopyFunctionComplex.RightResolutionMapping
