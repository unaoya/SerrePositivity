module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Anodyne.KanTwoHornLift
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CurriedHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# Kan fibrationの基底上で一定となるようにレトラクションのホモトピーを補正する

## 概要
Kan fibrationの基底上で一定となるようにレトラクションのホモトピーを補正する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0410][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0410
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Correct a retraction homotopy to be constant over its Kan-fibration base

The correction fills the two-horn with the original homotopy and its
section-projected loop. No model structure or weak-equivalence axiom is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanFiberwiseContraction

private lemma face_zero_sigma :
    SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

private lemma face_one_sigma :
    SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  have h : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

private lemma face_two_sigma :
    SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  have h : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by decide
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp]
  rfl

private lemma vertex_zero :
    SSet.stdSimplex.δ.{v} (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

private lemma vertex_one :
    SSet.stdSimplex.δ.{v} (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

variable {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (H : SSet.Homotopy (𝟙 E) (p ≫ s))

def sectionLoop : SSet.Homotopy (p ≫ s) (p ≫ s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (HomotopyClasses.postHomotopy (p ≫ s) H)
    (Category.id_comp _) (by
      rw [Category.assoc p s (p ≫ s), ← Category.assoc s p s, hs, Category.id_comp])

def baseLoop : SSet.Homotopy p p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (HomotopyClasses.postHomotopy p H)
    (Category.id_comp _) (by simp only [Category.assoc, hs, Category.comp_id])

lemma sectionLoop_h : (sectionLoop p s hs H).h = H.h ≫ (p ≫ s) := by
  rw [sectionLoop, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
  rfl

lemma baseLoop_h : (baseLoop p s hs H).h = H.h ≫ p := by
  rw [baseLoop, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
  rfl

include hp hs H in
/-- Kan fibrationの基底上で一定となるようにレトラクションのホモトピーを補正する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
lemma exists_homotopy : ∃ V : SSet.Homotopy (𝟙 E) (p ≫ s),
    V.h ≫ p = fst E (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) ≫ p := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have hq : SSet.modelCategoryQuillen.J.rlp ((ihom E).map p) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  let e₀ := curry (sectionLoop p s hs H).h
  let e₁ := curry H.h
  let b := SSet.stdSimplex.σ (0 : Fin 2) ≫ curry (baseLoop p s hs H).h
  have hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ e₀ =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ e₁ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one (sectionLoop p s hs H)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one H).symm
  have h₀ : e₀ ≫ (ihom E).map p = SSet.stdSimplex.δ (0 : Fin 3) ≫ b := by
    dsimp only [e₀, b]
    rw [← Category.assoc, face_zero_sigma, Category.id_comp, ← curry_natural_right]
    rw [sectionLoop_h, baseLoop_h]
    simp only [Category.assoc, hs, Category.comp_id]
  have h₁ : e₁ ≫ (ihom E).map p = SSet.stdSimplex.δ (1 : Fin 3) ≫ b := by
    dsimp only [e₁, b]
    rw [← Category.assoc, face_one_sigma, Category.id_comp, ← curry_natural_right]
    rw [baseLoop_h]
  obtain ⟨t, ht₀, ht₁, htp⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_triangle ((ihom E).map p) hq e₀ e₁ b hc h₀ h₁
  have hz : SSet.stdSimplex.δ (1 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point (𝟙 E) := by
    rw [← Category.assoc, vertex_zero, Category.assoc, ht₁]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero H
  have ho : SSet.stdSimplex.δ (0 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point (p ≫ s) := by
    rw [← Category.assoc, vertex_one, Category.assoc, ht₀]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero (sectionLoop p s hs H)
  refine ⟨CurriedHomotopy.ofEdge (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) hz ho, ?_⟩
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) ≫ p = _
  rw [← uncurry_natural_right, Category.assoc, htp]
  dsimp only [b]
  rw [← Category.assoc, face_two_sigma, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero (baseLoop p s hs H), uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point, uncurry_curry]
  rfl

end SerrePositivity.SimplicialModel.KanFiberwiseContraction
