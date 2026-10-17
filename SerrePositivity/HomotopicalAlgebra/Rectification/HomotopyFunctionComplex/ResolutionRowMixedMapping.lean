module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionFrameRowFunctor
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedHomBifunctor
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionInvariance

/-!
# 中断した任意モデル源への一般化：ResolutionRowMixedMapping

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual resolution rows of the same mixed output, natural in all presentations。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0330][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0330
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual resolution rows of the same mixed output, natural in all presentations

The row augmentations have identity base maps. They are maps of genuine
resolutions, rather than only objectwise weakly equivalent diagrams.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionRowMixedMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

def rowPoints : SimplexCategoryᵒᵖ ⥤ (FramedResolution C)ᵒᵖ ⥤ (SimplexCategory ⥤ C)ᵒᵖ where
  obj n := (FramedResolution.outerDiagrams ⋙
    (evaluation SimplexCategory (SimplexCategory ⥤ C)).obj n.unop).op
  map θ :=
    { app X := ((ResolutionLiftSpace.frame X.unop.inner).obj.map θ.unop).op
      naturality {X Y} f := by
        apply Quiver.Hom.unop_inj
        exact f.unop.frame.naturality θ.unop }
  map_id n := by
    apply NatTrans.ext
    funext X
    apply Quiver.Hom.unop_inj
    exact (ResolutionLiftSpace.frame X.unop.inner).obj.map_id n.unop
  map_comp θ σ := by
    apply NatTrans.ext
    funext X
    apply Quiver.Hom.unop_inj
    exact (ResolutionLiftSpace.frame X.unop.inner).obj.map_comp σ.unop θ.unop

def presentations : SimplexCategoryᵒᵖ ⥤ RightResolutionMapping.Index C ⥤
    (SimplexCategory ⥤ C)ᵒᵖ × (SimplexCategory ⥤ Cᵒᵖ)ᵒᵖ where
  obj n := (rowPoints.obj n).prod ((rowPoints (C := Cᵒᵖ)).obj n)
  map θ := NatTrans.prod (rowPoints.map θ) ((rowPoints (C := Cᵒᵖ)).map θ)
  map_id n := by
    apply NatTrans.ext
    funext X
    exact Prod.ext (congr_app (rowPoints.map_id n) X.1)
      (congr_app ((rowPoints (C := Cᵒᵖ)).map_id n) X.2)
  map_comp θ σ := by
    apply NatTrans.ext
    funext X
    exact Prod.ext (congr_app (rowPoints.map_comp θ σ) X.1)
      (congr_app ((rowPoints (C := Cᵒᵖ)).map_comp θ σ) X.2)

abbrev rows : SimplexCategoryᵒᵖ ⥤ RightResolutionMapping.Index C ⥤ SSet.{v} :=
  presentations ⋙ (Functor.whiskeringRight (RightResolutionMapping.Index C)
    ((SimplexCategory ⥤ C)ᵒᵖ × (SimplexCategory ⥤ Cᵒᵖ)ᵒᵖ) SSet.{v}).obj MixedDiagonalHom.functor

abbrev diagonal : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  (rows (C := C)).flip ⋙ SerrePositivity.BisimplicialModel.diagonal

lemma row_value (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    (rows.obj n).obj R = MixedDiagonalHom.obj
      (ResolutionFrameRows.row R.1.unop.inner n.unop).resolution.obj
      (ResolutionFrameRows.row R.2.unop.inner n.unop).resolution.obj := rfl

def rowComparison (n : SimplexCategoryᵒᵖ) :
    MixedBiresolutionComparison.functor (C := C) ⟶ rows.obj n where
  app R := MixedDiagonalHom.map
    (ResolutionFrameRows.augmentation R.1.unop.inner n.unop).diagram
    (ResolutionFrameRows.augmentation R.2.unop.inner n.unop).diagram
  naturality {R S} f := by
    change MixedDiagonalHom.map f.1.unop.map.diagram f.2.unop.map.diagram ≫
        MixedDiagonalHom.map ((ResolutionLiftSpace.frame S.1.unop.inner).augmentation.app n.unop)
          ((ResolutionLiftSpace.frame S.2.unop.inner).augmentation.app n.unop) =
      MixedDiagonalHom.map ((ResolutionLiftSpace.frame R.1.unop.inner).augmentation.app n.unop)
          ((ResolutionLiftSpace.frame R.2.unop.inner).augmentation.app n.unop) ≫
        MixedDiagonalHom.map (f.1.unop.frame.app n.unop) (f.2.unop.frame.app n.unop)
    rw [← MixedDiagonalHom.map_comp, ← MixedDiagonalHom.map_comp]
    exact congrArg₂ MixedDiagonalHom.map (congr_app f.1.unop.over n.unop).symm
      (congr_app f.2.unop.over n.unop).symm

def comparison : (Functor.const SimplexCategoryᵒᵖ).obj
    (MixedBiresolutionComparison.functor (C := C)) ⟶ rows where
  app := rowComparison
  naturality {n m} θ := by
    apply NatTrans.ext
    funext R
    change 𝟙 _ ≫ MixedDiagonalHom.map
        ((ResolutionLiftSpace.frame R.1.unop.inner).augmentation.app m.unop)
        ((ResolutionLiftSpace.frame R.2.unop.inner).augmentation.app m.unop) =
      MixedDiagonalHom.map ((ResolutionLiftSpace.frame R.1.unop.inner).augmentation.app n.unop)
        ((ResolutionLiftSpace.frame R.2.unop.inner).augmentation.app n.unop) ≫ MixedDiagonalHom.map
        ((ResolutionLiftSpace.frame R.1.unop.inner).obj.map θ.unop)
        ((ResolutionLiftSpace.frame R.2.unop.inner).obj.map θ.unop)
    rw [Category.id_comp, ← MixedDiagonalHom.map_comp]
    exact congrArg₂ MixedDiagonalHom.map
      (ResolutionFrameRows.row_operator_augmentation R.1.unop.inner θ.unop).symm
      (ResolutionFrameRows.row_operator_augmentation R.2.unop.inner θ.unop).symm

def componentIso (R : RightResolutionMapping.Index C) :
    (diagonal (C := C)).obj R ≅ (MixedResolutionComparison.output (C := C)).obj R :=
  NatIso.ofComponents (fun _ => (Equiv.refl _).toIso) (by
    intro n m θ
    ext h
    let A := (ResolutionLiftSpace.frame R.1.unop.inner).obj
    let B := (ResolutionLiftSpace.frame R.2.unop.inner).obj
    change (A.obj m.unop).map θ.unop ≫
        ((A.map θ.unop).app n.unop ≫ h ≫ ((B.map θ.unop).app n.unop).unop) ≫
          ((B.obj m.unop).map θ.unop).unop =
      ((A.map θ.unop).app m.unop ≫ (A.obj n.unop).map θ.unop) ≫ h ≫
        ((B.map θ.unop).app m.unop ≫ (B.obj n.unop).map θ.unop).unop
    calc
      _ = ((A.obj m.unop).map θ.unop ≫ (A.map θ.unop).app n.unop) ≫ h ≫
          ((B.obj m.unop).map θ.unop ≫ (B.map θ.unop).app n.unop).unop := by
        simp only [unop_comp, Category.assoc]
      _ = _ := by rw [(A.map θ.unop).naturality θ.unop, (B.map θ.unop).naturality θ.unop])

/-- The entire diagonal is the same mixed output used by the original lift action. -/
def diagonalIso : diagonal (C := C) ≅ MixedResolutionComparison.output :=
  NatIso.ofComponents componentIso (by
    intro R S f
    ext n h
    rfl)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma rowComparison_weakEquivalence (R : RightResolutionMapping.Index C)
    (n : SimplexCategoryᵒᵖ) : weakEquivalences SSet.{v} ((rowComparison n).app R) :=
  MixedResolutionInvariance.lift_map_weakEquivalence hcof hfib
    (ResolutionFrameRows.augmentation R.1.unop.inner n.unop)
    (ResolutionFrameRows.augmentation R.2.unop.inner n.unop)
    ((weakEquivalences C).id_mem _) ((weakEquivalences Cᵒᵖ).id_mem _)

include hcof hfib in
lemma row_operator_weakEquivalence (R : RightResolutionMapping.Index C)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    weakEquivalences SSet.{v} ((rows.map θ).app R) := by
  have h := congr_app ((comparison (C := C)).naturality θ) R
  change 𝟙 _ ≫ (rowComparison m).app R = (rowComparison n).app R ≫ (rows.map θ).app R at h
  rw [Category.id_comp] at h
  exact (weakEquivalences SSet.{v}).of_precomp _ _
    (rowComparison_weakEquivalence hcof hfib R n)
    (h ▸ rowComparison_weakEquivalence hcof hfib R m)

end SerrePositivity.HomotopyFunctionComplex.ResolutionRowMixedMapping
