module

public import SerrePositivity.KST.Descent.AugmentedCechSpaces
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation

/-!
# 実際の指定 Čech 降下の比較と反映

## 概要
指定増強つき図式の同型と、元と図式の各点が弱同値な射について、実際の降下条件を比較する。

## 方針
指定増強の自然性を Arrow の射・同型にし、模型の弱同値の同型不変性と飽和性を使う。

## 規約
指定写像を保持する可換正方形を構成し、降下の同値を独立の仮定にしない。

## 使われ方
論文 補題 3.2・3.3 の各行・細分・置換による実際の指定比較の移送。
-/

@[expose] public section

noncomputable section

universe u vH uH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：指定増強つき図式の同型は実際の降下条件を保持（補題 3.2）。
方針：指定増強の自然性と両射影の同型から Arrow の同型を構成する。
規約：増強元と図式の同型を両方保持する。使われ方：指定 curry 同型による移送。 -/
theorem cechSpaceDescent_iso_iff {A B : AugmentedCechDiagram K} (e : A ≅ B) :
    HasCechSpaceDescent K I J A ↔ HasCechSpaceDescent K I J B := by
  let E : Arrow.mk ((homotopyCechAugmentation K I J).app A) ≅
      Arrow.mk ((homotopyCechAugmentation K I J).app B) :=
    Arrow.isoMk ((cechAugmentedSource K).mapIso e)
      ((cechAugmentedDiagram K ⋙ HomotopyCones.functor K I J).mapIso e)
      ((homotopyCechAugmentation K I J).naturality e.hom)
  exact (weakEquivalences SSet.{u}).arrow_mk_iso_iff E

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]
  {H : Type uH} [Category.{vH} H]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]

include Λ in
/-- 概要：増強元と図式の各点が弱同値な射は実際の降下条件を反映（補題 3.2・3.3）。
方針：実際のホモトピー極限による弱同値の保存と、局所化後の可換正方形を使う。
規約：図式の fibrancy は不要。使われ方：実際の置換と細分比較の弱同値の移送。 -/
theorem cechSpaceDescent_map_iff {A B : AugmentedCechDiagram K} (f : A ⟶ B)
    (hl : weakEquivalences SSet.{u} f.left)
    (hr : ∀ k, weakEquivalences SSet.{u} (f.right.app k)) :
    HasCechSpaceDescent K I J A ↔ HasCechSpaceDescent K I J B := by
  let a : Arrow.mk ((homotopyCechAugmentation K I J).app A) ⟶
      Arrow.mk ((homotopyCechAugmentation K I J).app B) :=
    Arrow.homMk f.left ((HomotopyCones.functor K I J).map f.right)
      ((homotopyCechAugmentation K I J).naturality f)
  exact (Quillen.weakEquivalences_iff_isIso_map Λ _).trans
    ((Quillen.isIso_map_iff_of_weak_square Λ a hl
      (HomotopyCones.map_weakEquivalence K I J f.right hr)).trans
        (Quillen.weakEquivalences_iff_isIso_map Λ _).symm)

/-- 概要：局所化を内部構成した弱同値な増強つき図式の実際の降下の反映（補題 3.2）。
方針：Mathlib の実際の局所化関手を比較定理へ渡す。
規約：局所化関手の追加入力は不要。使われ方：実際の置換・細分の指定比較の移送。 -/
theorem cechSpaceDescent_map_iff_canonical {A B : AugmentedCechDiagram K} (f : A ⟶ B)
    (hl : weakEquivalences SSet.{u} f.left)
    (hr : ∀ k, weakEquivalences SSet.{u} (f.right.app k)) :
    HasCechSpaceDescent K I J A ↔ HasCechSpaceDescent K I J B :=
  cechSpaceDescent_map_iff K I J (weakEquivalences SSet.{u}).Q f hl hr

end SerrePositivity.KST.Descent
