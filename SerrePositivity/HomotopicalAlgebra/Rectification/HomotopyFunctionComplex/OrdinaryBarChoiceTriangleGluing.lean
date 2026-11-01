module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryTensorGluing
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceTriangleGluing

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Glue three actual parameterized choice morphisms with their endpoint equations。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0145][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0145
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Glue three actual parameterized choice morphisms with their endpoint equations

The three original base arrows need not be definitionally equal. Their
actual endpoint equations supply the equalities used to relabel choices.
No model structure on the larger simplicial-set universe is used.
-/

@[expose] public section
universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing

abbrev interval := SSet.stdSimplex.{w}.obj (SimplexCategory.mk 1)
abbrev point := SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0)

lemma tensor_face_zero (P : SSet.{w}) :
    P ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst P point ≫ SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [whiskerLeft_fst, Category.assoc, SSet.ι₁_fst, Category.comp_id]
  · rw [whiskerLeft_snd, SSet.stdSimplex.δ_zero_eq_const, Category.assoc,
      SSet.ι₁_snd, SSet.comp_const, SSet.comp_const]

lemma tensor_face_one (P : SSet.{w}) :
    P ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst P point ≫ SSet.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [whiskerLeft_fst, Category.assoc, SSet.ι₀_fst, Category.comp_id]
  · rw [whiskerLeft_snd, SSet.stdSimplex.δ_one_eq_const, Category.assoc,
      SSet.ι₀_snd, SSet.comp_const, SSet.comp_const]

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

lemma relabel_refl {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    OrdinaryBarChoiceComposition.relabel hcof hfib (rfl : f = f) = 𝟙 _ := rfl

lemma reindex_extension {Q R : SSet.{max u v}}
    {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib Q} (j : R ⟶ Q) (a : X ⟶ Y) :
    ((OrdinaryBarChoiceCategory.reindex hcof hfib j).map a).extension = j ≫ a.extension := rfl

lemma normalized_extension_eq {Q : SSet.{max u v}}
    {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib Q} (a b : X ⟶ Y)
    (h : a = b) (f : X.base ⟶ Y.base) (ha : a.base = f) (hb : b.base = f) :
    a.extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib ha =
      b.extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib hb := by
  subst b
  rfl

variable {P : SSet.{max u v}}
  {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (P ⊗ interval)}
  (a b c : X ⟶ Y)
  (h0 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map a =
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map b)
  (h1 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map a =
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map c)
  (h2 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map b =
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map c)

include h0 in
lemma baseB : b.base = a.base := (congrArg OrdinaryBarChoiceCategory.Hom.base h0).symm
include h1 in
lemma baseC : c.base = a.base := (congrArg OrdinaryBarChoiceCategory.Hom.base h1).symm

def edge02 : P ⊗ interval ⟶ OrdinaryBarRetractSystem.choices hcof hfib a.base :=
  b.extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib (baseB hcof hfib a b h0)

def edge12 : P ⊗ interval ⟶ OrdinaryBarRetractSystem.choices hcof hfib a.base :=
  c.extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib (baseC hcof hfib a c h1)

lemma overlap0 : SSet.ι₀ ≫ edge02 hcof hfib a b h0 = SSet.ι₀ ≫ a.extension := by
  simpa only [edge02, reindex_extension, Category.assoc, relabel_refl,
    Category.comp_id] using normalized_extension_eq hcof hfib
      ((OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map b)
      ((OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map a)
      h0.symm a.base (baseB hcof hfib a b h0) rfl

lemma overlap1 : SSet.ι₁ ≫ a.extension = SSet.ι₀ ≫ edge12 hcof hfib a c h1 := by
  simpa only [edge12, reindex_extension, Category.assoc, relabel_refl,
    Category.comp_id] using normalized_extension_eq hcof hfib
      ((OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map a)
      ((OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map c)
      h1 a.base rfl (baseC hcof hfib a c h1)

set_option maxHeartbeats 800000 in
-- Reduction compares two reindexed dependent choices with different base-equality proofs.
lemma overlap2
    (h2 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map b =
      (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map c) :
    SSet.ι₁ ≫ edge02 hcof hfib a b h0 =
    SSet.ι₁ ≫ edge12 hcof hfib a c h1 := by
  simpa only [edge02, edge12, reindex_extension, Category.assoc] using
    normalized_extension_eq hcof hfib
    ((OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map b)
    ((OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map c)
    h2 a.base (baseB hcof hfib a b h0) (baseC hcof hfib a c h1)

abbrev faces : Fin 3 → (P ⊗ interval ⟶ OrdinaryBarRetractSystem.choices hcof hfib a.base) :=
  ![edge12 hcof hfib a c h1, edge02 hcof hfib a b h0, a.extension]

include h2 in
lemma compatible : BoundaryTensorGluing.Compatible (faces hcof hfib a b c h0 h1) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · change P ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ edge12 hcof hfib a c h1 =
      P ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ edge02 hcof hfib a b h0
    rw [tensor_face_zero, Category.assoc, Category.assoc, overlap2 hcof hfib a b c h0 h1 h2]
  · change P ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ edge12 hcof hfib a c h1 =
      P ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ a.extension
    rw [tensor_face_one, tensor_face_zero, Category.assoc, Category.assoc,
      overlap1 hcof hfib a c h1]
  · change P ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ edge02 hcof hfib a b h0 =
      P ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ a.extension
    rw [tensor_face_one, Category.assoc, Category.assoc, overlap0 hcof hfib a b h0]

def boundary : P ⊗ (SSet.boundary 2).toSSet ⟶ OrdinaryBarRetractSystem.choices hcof hfib a.base :=
  BoundaryTensorGluing.desc (faces hcof hfib a b c h0 h1) (compatible hcof hfib a b c h0 h1 h2)

lemma boundary_face (k : Fin 3) : P ◁ SSet.boundary.ι k ≫ boundary hcof hfib a b c h0 h1 h2 =
    faces hcof hfib a b c h0 h1 k :=
  BoundaryTensorGluing.desc_fac _ _ k

def boundaryObject (Z : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (P ⊗ interval)) :
    OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (P ⊗ (SSet.boundary 2).toSSet) :=
  ⟨Z.base⟩

def boundaryHom : boundaryObject hcof hfib X ⟶ boundaryObject hcof hfib Y :=
  ⟨a.base, boundary hcof hfib a b c h0 h1 h2⟩

lemma boundaryHom_face2 :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (2 : Fin 3))).map
      (boundaryHom hcof hfib a b c h0 h1 h2) = a := by
  exact congrArg (fun s => (⟨a.base, s⟩ : X ⟶ Y))
    (boundary_face hcof hfib a b c h0 h1 h2 2)

lemma boundaryHom_face1 :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (1 : Fin 3))).map
      (boundaryHom hcof hfib a b c h0 h1 h2) = b := by
  exact (congrArg (fun s => (⟨a.base, s⟩ : X ⟶ Y))
    (boundary_face hcof hfib a b c h0 h1 h2 1)).trans
      (OrdinaryBarFreeDiagramHomotopy.normalized_eq hcof hfib a b (baseB hcof hfib a b h0))

lemma boundaryHom_face0 :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (0 : Fin 3))).map
      (boundaryHom hcof hfib a b c h0 h1 h2) = c := by
  exact (congrArg (fun s => (⟨a.base, s⟩ : X ⟶ Y))
    (boundary_face hcof hfib a b c h0 h1 h2 0)).trans
      (OrdinaryBarFreeDiagramHomotopy.normalized_eq hcof hfib a c (baseC hcof hfib a c h1))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing
