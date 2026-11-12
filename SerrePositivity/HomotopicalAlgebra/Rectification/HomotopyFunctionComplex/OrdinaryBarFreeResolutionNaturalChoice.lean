module

public import SerrePositivity.CategoryTheory.Simplex.Naturality
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreePathSimplicialResolution

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionNaturalChoice

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual coherent free choices as a natural transformation on the usual simplex category。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0186][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0186
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual coherent free choices as a natural transformation on the usual simplex category

The source is the reversed actual free-path resolution. The components are
the constructed choice functors transported by the proved degree comparison.
All simplex maps satisfy naturality, not only the generating operators.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeResolutionSeed
variable {C : Type u} [Category.{v} C]

def source : SimplicialObject Cat.{max u v, u} :=
  SimplexCategory.rev.op ⋙ FreePathSimplicialResolution.diagram (D C)

lemma source_obj (n : ℕ) : (source (C := C)).obj (Opposite.op (SimplexCategory.mk n)) =
    ComonadResolutionOperators.power FreePathResolution.comonad
      (FreePathResolutionPresentation.base (D C)) (n + 1) := rfl

lemma source_face {n : ℕ} (i : Fin (n + 2)) : (source (C := C)).δ i =
    ComonadResolutionOperators.face FreePathResolution.comonad
      (FreePathResolutionPresentation.base (D C)) (n + 1) i.rev := by
  change (FreePathSimplicialResolution.diagram (D C)).map
    (SimplexCategory.rev.map (SimplexCategory.δ i)).op = _
  rw [SimplexCategory.rev_map_δ]
  exact ComonadSimplicialResolution.diagram_face _ _ i.rev

lemma source_degeneracy {n : ℕ} (i : Fin (n + 1)) : (source (C := C)).σ i =
    ComonadResolutionOperators.degeneracy FreePathResolution.comonad
      (FreePathResolutionPresentation.base (D C)) n i.rev := by
  change (FreePathSimplicialResolution.diagram (D C)).map
    (SimplexCategory.rev.map (SimplexCategory.σ i)).op = _
  rw [SimplexCategory.rev_map_σ]
  exact ComonadSimplicialResolution.diagram_degeneracy _ _ i.rev

variable [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev target := OrdinaryBarParameterChoiceCategory.diagram (C := C) hcof hfib P

def component (n : SimplexCategoryᵒᵖ) :
    (source (C := C)).obj n ⟶ (target (C := C) hcof hfib P).obj n :=
  eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫
    (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom

lemma component_face {n : ℕ} (i : Fin (n + 2)) : (source (C := C)).δ i ≫
    component (C := C) hcof hfib P (Opposite.op (SimplexCategory.mk n)) =
      component (C := C) hcof hfib P (Opposite.op (SimplexCategory.mk (n + 1))) ≫
        (target (C := C) hcof hfib P).δ i := by
  rw [source_face]
  apply (cancel_epi (eqToHom (degree_power (D C) (n + 2)))).1
  change eqToHom (degree_power (D C) (n + 2)) ≫
      (ComonadResolutionOperators.face FreePathResolution.comonad
        (FreePathResolutionPresentation.base (D C)) (n + 1) i.rev ≫
      (eqToHom (degree_power (D C) (n + 1)).symm ≫
        (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n).toCatHom)) = _
  rw [← Category.assoc (eqToHom (degree_power (D C) (n + 2))),
    ← face_comparison (D C) (n + 1) i.rev]
  simp only [component, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [OrdinaryBarParameterChoiceCategory.diagram_face]
  apply Cat.Hom.ext
  change faceFunctor (D C) (n + 1) i.rev ⋙
      OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n = _
  simpa only [fixedFace_eq, reverseFace, Cat.Hom.comp_toFunctor,
    Functor.toCatHom_toFunctor] using
    (OrdinaryBarFreeResolutionChoices.diagram_face (C := C) hcof hfib P n i).symm

lemma component_degeneracy {n : ℕ} (i : Fin (n + 1)) : (source (C := C)).σ i ≫
    component (C := C) hcof hfib P (Opposite.op (SimplexCategory.mk (n + 1))) =
      component (C := C) hcof hfib P (Opposite.op (SimplexCategory.mk n)) ≫
        (target (C := C) hcof hfib P).σ i := by
  rw [source_degeneracy]
  apply (cancel_epi (eqToHom (degree_power (D C) (n + 1)))).1
  change eqToHom (degree_power (D C) (n + 1)) ≫
      (ComonadResolutionOperators.degeneracy FreePathResolution.comonad
        (FreePathResolutionPresentation.base (D C)) n i.rev ≫
      (eqToHom (degree_power (D C) (n + 2)).symm ≫
        (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P (n + 1)).toCatHom)) = _
  rw [← Category.assoc (eqToHom (degree_power (D C) (n + 1))),
    ← degeneracy_comparison (D C) n i.rev]
  simp only [component, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [OrdinaryBarParameterChoiceCategory.diagram_degeneracy]
  apply Cat.Hom.ext
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma, Fin.rev_rev,
    Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor, CosimplicialObject.σ] using
    OrdinaryBarFreeResolutionChoices.diagram_degeneracy (C := C) hcof hfib P n i.rev

def choices : source (C := C) ⟶ target (C := C) hcof hfib P :=
  SimplexNaturality.ofFacesDegeneracies _ _ (component (C := C) hcof hfib P)
    (component_face hcof hfib P) (component_degeneracy hcof hfib P)

lemma choices_app (n : SimplexCategoryᵒᵖ) : (choices (C := C) hcof hfib P).app n =
    component (C := C) hcof hfib P n := rfl

def augmentation : source (C := C) ⟶
    (Functor.const _).obj (FreePathResolutionPresentation.base (D C)) :=
  choices hcof hfib P ≫ OrdinaryBarParameterChoiceCategory.projection hcof hfib P

lemma augmentation_app (n : SimplexCategoryᵒᵖ) :
    (augmentation (C := C) hcof hfib P).app n =
      eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫
        (OrdinaryBarFreeResolutionChoices.augmentation (C := C) n.unop.len ⋙
          ULiftHom.up.{v, u, u}).toCatHom := by
  change (eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫
    (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom) ≫
      (OrdinaryBarParameterChoiceCategory.baseProjection hcof hfib P n).toCatHom = _
  rw [Category.assoc]
  congr 1
  apply Cat.Hom.ext
  change OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len ⋙
      (OrdinaryBarChoiceCategory.projection hcof hfib _ ⋙ ULiftHom.up.{v, u, u}) = _
  rw [← CategoryTheory.Functor.assoc]
  exact congrArg (fun F => F ⋙ ULiftHom.up.{v, u, u})
    (OrdinaryBarFreeResolutionChoices.projection_eq_augmentation hcof hfib P n.unop.len)

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma augmentation_comparison (n : ℕ) :
    (OrdinaryBarFreeResolutionChoices.augmentation (C := C) n ⋙
      ULiftHom.up.{v, u, u}).toCatHom =
    eqToHom (degree_power (D C) (n + 1)) ≫
      ComonadResolutionOperators.augmentation FreePathResolution.comonad
        (FreePathResolutionPresentation.base (D C)) (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change faceHom (D C) (n + 1) 0 ≫
        (OrdinaryBarFreeResolutionChoices.augmentation (C := C) n ⋙
          ULiftHom.up.{v, u, u}).toCatHom = _
    rw [ih, ← Category.assoc, face_comparison_zero, Category.assoc]
    rfl

lemma augmentation_eq_standard : augmentation (C := C) hcof hfib P =
    Functor.whiskerLeft SimplexCategory.rev.op
      (FreePathSimplicialResolution.augmentation (D C)) := by
  apply NatTrans.ext
  funext n
  rw [augmentation_app, augmentation_comparison]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice
