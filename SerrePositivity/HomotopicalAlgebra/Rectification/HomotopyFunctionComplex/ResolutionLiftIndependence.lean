module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCategoryHom
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantComparison

/-!
# 中断した任意モデル源への一般化：ResolutionLiftIndependence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Independence of resolution lifts in the homotopy category of spaces。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0307][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0307
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Independence of resolution lifts in the homotopy category of spaces

All lifts of the same base map induce the same map after localizing the
actual simplicial Hom. This is equality in Ho(SSet), not only on components.
No functorial factorization is required on the source.
-/

@[expose] public section
universe v u vS uS
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {H : Type uS} [Category.{vS} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]

include hcof in
lemma hom_map_eq_of_base_eq {X X' : (ResolutionObject C)ᵒᵖ}
    (f g : X ⟶ X') (h : f.unop.base = g.unop.base) (Y : FibrantObject C) :
    L.map ((hom.map f).app Y) = L.map ((hom.map g).app Y) := by
  let := simplexModelCategory C
  let D := SimplexCategory ⥤ C
  let Q := (weakEquivalences D).Q
  have haug : IsIso (Q.map X.unop.resolution.augmentation) :=
    Localization.inverts Q (weakEquivalences D) _ X.unop.resolution.augmentation_weakEquivalence
  have he : Q.map f.unop.diagram = Q.map g.unop.diagram := by
    apply (cancel_mono (Q.map X.unop.resolution.augmentation)).mp
    rw [← Q.map_comp, f.unop.over, ← Q.map_comp, g.unop.over, h]
  have hX : IsCofibrant X.unop.resolution.obj := ⟨X.unop.resolution.cofibrant⟩
  have hX' : IsCofibrant X'.unop.resolution.obj := ⟨X'.unop.resolution.cofibrant⟩
  let F : CofibrantObject D ⥤ Hᵒᵖ :=
    CofibrantObject.ι ⋙ (cosimplicialHomSource Y.obj).rightOp ⋙ L.op
  have hF : (weakEquivalences (CofibrantObject D)).IsInvertedBy F := by
    intro A B a ha
    have ha' : ∀ n, weakEquivalences C (a.hom.app n) := ha
    have hw := cosimplicialHomMap_weakEquivalence hcof a.hom
      (mem_cofibrations (initial.to A.obj)) (mem_cofibrations (initial.to B.obj)) ha' Y.obj
    have : IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a.hom).app Y.obj)) :=
      Localization.inverts L (weakEquivalences SSet.{v}) _ hw
    exact inferInstanceAs (IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a.hom).app Y.obj)).op)
  have he' : (CofibrantObject.ι ⋙ Q).map (CofibrantObject.homMk f.unop.diagram) =
      (CofibrantObject.ι ⋙ Q).map (CofibrantObject.homMk g.unop.diagram) := he
  have eqF := (AreEqualizedByLocalization.mk _ _ _
    (CofibrantObject.ι ⋙ Q) he').map_eq_of_isInvertedBy F hF
  exact Quiver.Hom.op_inj eqF

end SerrePositivity.HomotopyFunctionComplex.ResolutionObject
