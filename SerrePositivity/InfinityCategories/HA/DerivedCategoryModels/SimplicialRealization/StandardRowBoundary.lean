module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
# 実現の横微分と元の全ての面の境界

## 概要
添字延長の横微分を元の単体次数へ戻し、すべての面の交代和と照合する。

## 方針
同じ延長の次数同型の下で微分を計算し、元の交代面複体の式を使う。

## 規約
面の順序と符号を変えず、同じ行の同型を保つ。

## 使われ方
HA 1.2.4。strict coherent bar の一次列と全複体の同じ微分の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Preadditive AlgebraicTopology
open SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 隣接する二行の横微分は、元の交代面微分と同じ射。 -/
theorem doubleComplexRow_d (X : SimplicialObject (Complex A)) (n : ℕ) :
    (doubleComplexRowIso A X (n + 1)).inv ≫
        ((doubleComplexFunctor A).obj X).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (AlternatingFaceMapComplex.obj X).d (n + 1) n ≫ (doubleComplexRowIso A X n).inv := by
  let K := AlternatingFaceMapComplex.obj X
  have hi : SerrePositivity.embUp.f (n + 1) = -((n + 1 : ℕ) : ℤ) := by
    change (0 : ℤ) - ((n + 1 : ℕ) : ℤ) = -((n + 1 : ℕ) : ℤ)
    omega
  have hj : SerrePositivity.embUp.f n = -(n : ℤ) := by
    change (0 : ℤ) - (n : ℤ) = -(n : ℤ)
    omega
  change (K.extendXIso SerrePositivity.embUp hi).inv ≫
    (K.extend SerrePositivity.embUp).d _ _ = _
  rw [K.extend_d_eq SerrePositivity.embUp hi hj, Iso.inv_hom_id_assoc]
  rfl

/-- 元のすべての面の交代和で書いた、同じ二行間の微分。 -/
theorem doubleComplexRow_d_faces (X : SimplicialObject (Complex A)) (n : ℕ) :
    (doubleComplexRowIso A X (n + 1)).inv ≫
        ((doubleComplexFunctor A).obj X).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • X.δ i) ≫ (doubleComplexRowIso A X n).inv := by
  rw [doubleComplexRow_d, AlternatingFaceMapComplex.obj_d_eq]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
