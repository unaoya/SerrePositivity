module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarMappingClasses
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-!
# 中断した任意モデル源への一般化：OrdinaryRawLabelHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Equal localized labels are joined by an actual mixed resolution edge。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0252][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0252
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Equal localized labels are joined by an actual mixed resolution edge

A good cylinder from the source resolution supplies the homotopy. The
target degeneracy embeds that homotopy in the raw diagonal. No value model
structure or selected functorial source factorization is used.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
  (R : OrdinaryResolutionPairs.Index (C := C))

lemma map_eq_of_label_eq
    {f g : (OrdinaryResolutionPairs.raw.obj R).obj (op (SimplexCategory.mk 0))}
    (h : OrdinaryMappingClassLabel.label Q R _ f = OrdinaryMappingClassLabel.label Q R _ g) :
    Q.map f = Q.map g := by
  have he := congrArg (LocalizedHomDiagram.equiv Q _) h
  rw [OrdinaryMappingClassLabel.label_equiv, OrdinaryMappingClassLabel.label_equiv] at he
  let a := OrdinaryMappingClassLabel.sourceIso Q R (SimplexCategory.mk 0)
  let b := OrdinaryMappingClassLabel.targetIso Q R (SimplexCategory.mk 0)
  have he' := congrArg (fun k => a.hom ≫ k ≫ b.hom) he
  simpa only [a, b, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using he'

def edgeOfLabelEq
    {f g : (OrdinaryResolutionPairs.raw.obj R).obj (op (SimplexCategory.mk 0))}
    (h : OrdinaryMappingClassLabel.label Q R _ f = OrdinaryMappingClassLabel.label Q R _ g) :
    (OrdinaryResolutionPairs.raw.obj R).Edge f g := by
  let A := R.1.unop.resolution
  let B := R.2.unop.resolution
  change A.obj.obj (SimplexCategory.mk 0) ⟶ (B.obj.obj (SimplexCategory.mk 0)).unop at f g
  have : IsCofibrant (A.obj.obj (SimplexCategory.mk 0)) := A.isCofibrant_obj _
  have : IsFibrant (B.obj.obj (SimplexCategory.mk 0)).unop :=
    DualResolutionTargets.isFibrant_obj C R.2 _
  have := cosimplicialCylinder_isGood A.obj A.cofibrant A.homotopicallyConstant
  have hh : LeftHomotopyRel f g := (LeftHomotopyRel.iff_map_eq Q _ _).mpr
    (map_eq_of_label_eq Q R h)
  let hom := hh.leftHomotopy (cosimplicialCylinder A.obj A.homotopicallyConstant)
  have hb (i : Fin 2) :
      (B.obj.map (SimplexCategory.σ (0 : Fin 1))).unop ≫
        (B.obj.map (SimplexCategory.δ i)).unop = 𝟙 _ := by
    rw [← unop_comp, ← B.obj.map_comp]
    have he : SimplexCategory.δ i ≫ SimplexCategory.σ (0 : Fin 1) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [he, B.obj.map_id, unop_id]
  have hh₀ : A.obj.map (SimplexCategory.δ (1 : Fin 2)) ≫ hom.h = f := hom.h₀
  have hh₁ : A.obj.map (SimplexCategory.δ (0 : Fin 2)) ≫ hom.h = g := hom.h₁
  refine SSet.Edge.ofTruncated
    { edge := hom.h ≫ (B.obj.map (SimplexCategory.σ (0 : Fin 1))).unop
      src_eq := ?_
      tgt_eq := ?_ }
  · change A.obj.map (SimplexCategory.δ (1 : Fin 2)) ≫
      (hom.h ≫ _) ≫ (B.obj.map (SimplexCategory.δ (1 : Fin 2))).unop = f
    simpa only [Category.assoc, hb, Category.comp_id] using hh₀
  · change A.obj.map (SimplexCategory.δ (0 : Fin 2)) ≫
      (hom.h ≫ _) ≫ (B.obj.map (SimplexCategory.δ (0 : Fin 2))).unop = g
    simpa only [Category.assoc, hb, Category.comp_id] using hh₁

lemma entry_component_eq
    {f g : (OrdinaryResolutionPairs.raw.obj R).obj (op (SimplexCategory.mk 0))}
    (h : OrdinaryMappingClassLabel.label Q R _ f = OrdinaryMappingClassLabel.label Q R _ g) :
    SSet.π₀.mk ((OrdinaryBarMappingClasses.entry R).app _ ⟨f⟩) =
      SSet.π₀.mk ((OrdinaryBarMappingClasses.entry R).app _ ⟨g⟩) := by
  let e := edgeOfLabelEq Q R h
  let lifted : (SSet.uliftFunctor.{max u v, v}.obj
      (OrdinaryResolutionPairs.raw.obj R)).Edge ⟨f⟩ ⟨g⟩ :=
    SSet.Edge.ofTruncated
      { edge := ⟨e.edge⟩
        src_eq := ULift.ext e.src_eq
        tgt_eq := ULift.ext e.tgt_eq }
  exact SSet.π₀.sound (lifted.map (OrdinaryBarMappingClasses.entry R))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy
