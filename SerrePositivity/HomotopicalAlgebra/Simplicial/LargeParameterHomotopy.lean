module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOne

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# 大きいパラメータから小さい可縮な比較空間の宇宙liftへの区間ホモトピーを構成する

## 概要
大きいパラメータから小さい可縮な比較空間の宇宙liftへの区間ホモトピーを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0442][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0442
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Homotopies of large-parameter maps into a lifted small injective space

Small boundary fillers assemble an actual interval homotopy. No model
structure is assumed in the larger universe.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.LargeParameterHomotopy

abbrev boundaryColimit (K : SSet.{r}) : IsColimit (BinaryCofan.mk
    (K ◁ SSet.boundary.ι.{r} (1 : Fin 2)) (K ◁ SSet.boundary.ι (0 : Fin 2))) :=
  mapIsColimitOfPreservesOfIsColimit ((curriedTensor SSet.{r}).obj K)
    (SSet.boundary.ι (1 : Fin 2)) (SSet.boundary.ι (0 : Fin 2))
    HomotopyFunctionComplex.BoundaryOne.isColimit

instance boundaryMono (K : SSet.{r}) : Mono (K ◁ (SSet.boundary.{r} 1).ι) := by
  have : ∀ n, Mono ((K ◁ (SSet.boundary.{r} 1).ι).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun x y h => by
      change (x.1, x.2.val) = (y.1, y.2.val) at h
      apply Prod.ext
      · exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1)).obj n => z.1) h
      · apply Subtype.ext
        exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1)).obj n => z.2) h)
  exact NatTrans.mono_of_mono_app _

abbrev vertexSection (K : SSet.{r}) : K ⟶ K ⊗ SSet.stdSimplex.{r}.obj (SimplexCategory.mk 0) :=
  lift (𝟙 K) (SSet.stdSimplex.isTerminalObj₀.from K)

lemma section_zero (K : SSet.{r}) :
    vertexSection K ≫ K ◁ SSet.stdSimplex.δ (1 : Fin 2) = SSet.ι₀ := by
  rw [SSet.stdSimplex.δ_one_eq_const]
  rfl

lemma section_one (K : SSet.{r}) :
    vertexSection K ≫ K ◁ SSet.stdSimplex.δ (0 : Fin 2) = SSet.ι₁ := by
  rw [SSet.stdSimplex.δ_zero_eq_const]
  rfl

section Boundary
variable {K Q : SSet.{r}} (e₀ e₁ : K ⟶ Q)

def boundaryMap : K ⊗ (SSet.boundary.{r} 1).toSSet ⟶ Q :=
  (boundaryColimit K).desc (BinaryCofan.mk (fst K _ ≫ e₀) (fst K _ ≫ e₁))

@[reassoc]
lemma boundaryMap_zero : K ◁ SSet.boundary.ι (1 : Fin 2) ≫ boundaryMap e₀ e₁ = fst K _ ≫ e₀ :=
  (boundaryColimit K).fac (BinaryCofan.mk (fst K _ ≫ e₀) (fst K _ ≫ e₁)) ⟨WalkingPair.left⟩

@[reassoc]
lemma boundaryMap_one : K ◁ SSet.boundary.ι (0 : Fin 2) ≫ boundaryMap e₀ e₁ = fst K _ ≫ e₁ :=
  (boundaryColimit K).fac (BinaryCofan.mk (fst K _ ≫ e₀) (fst K _ ≫ e₁)) ⟨WalkingPair.right⟩

end Boundary

variable {P : SSet.{v}} (hp : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers P) {K : SSet.{max w v}}
  (e₀ e₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)

def hom : K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P :=
  LargeParameterExtension.extend hp (K ◁ (SSet.boundary.{max w v} 1).ι) (boundaryMap e₀ e₁)

lemma face_zero : K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ hom hp e₀ e₁ = fst K _ ≫ e₀ := by
  rw [← SSet.boundary.ι_ι, whiskerLeft_comp, Category.assoc,
    hom, LargeParameterExtension.extend_initial, boundaryMap_zero]

lemma face_one : K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ hom hp e₀ e₁ = fst K _ ≫ e₁ := by
  rw [← SSet.boundary.ι_ι, whiskerLeft_comp, Category.assoc,
    hom, LargeParameterExtension.extend_initial, boundaryMap_one]

@[reassoc]
lemma at_zero : SSet.ι₀ ≫ hom hp e₀ e₁ = e₀ := by
  rw [← section_zero K, Category.assoc, face_zero]
  rfl

@[reassoc]
lemma at_one : SSet.ι₁ ≫ hom hp e₀ e₁ = e₁ := by
  rw [← section_one K, Category.assoc, face_one]
  rfl

/-- 大きいパラメータから小さい可縮な比較空間の宇宙liftへの区間ホモトピーを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def homotopy : SSet.Homotopy e₀ e₁ where
  h := hom hp e₀ e₁
  h₀ := at_zero hp e₀ e₁
  h₁ := at_one hp e₀ e₁
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.SimplicialModel.LargeParameterHomotopy
