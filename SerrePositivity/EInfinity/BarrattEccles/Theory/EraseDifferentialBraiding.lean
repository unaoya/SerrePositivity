module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialGraded
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric

/-!
# 次数付き比較を保った Koszul 対称性

## 概要
Berger–Moerdijk 命題 4.1 のセル付加で、微分を消したテンソルの対称性を照合する。

## 方針
忘却の強モノイダル比較で両端をそろえ、各斉次テンソルへの制限を計算する。

## 規約
次数付き余積の指定包含を用いる。

## 使われ方
微分を消す関手をオペラッド代数へ持ち上げる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open Functor.LaxMonoidal Functor.OplaxMonoidal
variable (A : Type u) [CommRing A]
local notation "U" => HomologicalComplex.forget (ModuleCat A) (ComplexShape.up ℤ)
attribute [local instance] complexGradedForgetMonoidal

@[reassoc]
lemma gradedInclusion_forget_tensor (K L : Complex A) (i j n : ℤ) (h : i + j = n) :
    GradedObject.Monoidal.ιTensorObj ((U).obj K) ((U).obj L) i j n h ≫
      (μ (U) K L) n = ιTensorObj K L i j n h := by
  change _ ≫ 𝟙 _ = _
  rfl

@[reassoc]
lemma complexInclusion_forget_delta (K L : Complex A) (i j n : ℤ) (h : i + j = n) :
    ιTensorObj K L i j n h ≫ (δ (U) K L) n =
      GradedObject.Monoidal.ιTensorObj ((U).obj K) ((U).obj L) i j n h := by
  change _ ≫ 𝟙 _ = _
  rfl

attribute [local irreducible] complexGradedForgetMonoidal

/-- The normalized symmetry depends only on the underlying graded modules. -/
lemma eraseDifferential_forget_normalized_braiding (K L : Complex A) :
    μ (U) ((eraseDifferential A).obj K) ((eraseDifferential A).obj L) ≫
      (U).map (β_ ((eraseDifferential A).obj K) ((eraseDifferential A).obj L)).hom ≫
      δ (U) ((eraseDifferential A).obj L) ((eraseDifferential A).obj K) =
    μ (U) K L ≫ (U).map (β_ K L).hom ≫ δ (U) L K := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j h
  change GradedObject.Monoidal.ιTensorObj ((U).obj K) ((U).obj L) i j n h ≫
      (μ (U) ((eraseDifferential A).obj K) ((eraseDifferential A).obj L)) n ≫
      (cochainTensorSymmetry ((eraseDifferential A).obj K)
        ((eraseDifferential A).obj L)).hom.f n ≫
      (δ (U) ((eraseDifferential A).obj L) ((eraseDifferential A).obj K)) n =
    GradedObject.Monoidal.ιTensorObj ((U).obj K) ((U).obj L) i j n h ≫
      (μ (U) K L) n ≫ (cochainTensorSymmetry K L).hom.f n ≫ (δ (U) L K) n
  erw [gradedInclusion_forget_tensor_assoc A ((eraseDifferential A).obj K)
    ((eraseDifferential A).obj L), gradedInclusion_forget_tensor_assoc A K L,
    ιTensorObj_cochainTensorSymmetry_assoc, ιTensorObj_cochainTensorSymmetry_assoc,
    Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
    complexInclusion_forget_delta, complexInclusion_forget_delta]
  rfl

end SerrePositivity.EInfinity
