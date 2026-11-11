module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialBraiding
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-!
# 微分を消す操作の対称モノイダル構造

## 概要
Berger–Moerdijk 命題 4.1 のセル付加を、次数付きの台で計算するための複体の比較。

## 方針
元の加群と射の次数成分を使い、テンソルの各斉次成分と点ごとの余極限を照合する。

## 規約
整数添字の余鎖複体と Koszul 符号を用いる。

## 使われ方
セル付加の次数付き自由表示。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
open DifferentialGraded

variable (A : Type u) [CommRing A]

local notation "U" => HomologicalComplex.forget (ModuleCat A) (ComplexShape.up ℤ)
open Functor.LaxMonoidal
open Functor.OplaxMonoidal (δ)
attribute [local instance] complexGradedForgetMonoidal
attribute [local irreducible] complexGradedForgetMonoidal

/-- 微分を消す操作のモノイダル構造。忘却の比較射を相殺して照合する。 -/
def eraseDifferentialCoreMonoidal : (eraseDifferential A).CoreMonoidal where
  εIso := eraseDifferentialUnitIso A
  μIso := eraseDifferentialTensorIso A
  μIso_hom_natural_left {K L} f M := by
    apply (U).map_injective
    apply (cancel_epi (μ (U) ((eraseDifferential A).obj K)
      ((eraseDifferential A).obj M))).mp
    simp only [CategoryTheory.Functor.map_comp]
    rw [← μ_natural_left_assoc, eraseDifferential_forget_tensor,
      eraseDifferential_forget_tensor_assoc, eraseDifferential_forget_map]
    exact μ_natural_left (U) f M
  μIso_hom_natural_right {K L} M f := by
    apply (U).map_injective
    apply (cancel_epi (μ (U) ((eraseDifferential A).obj M)
      ((eraseDifferential A).obj K))).mp
    simp only [CategoryTheory.Functor.map_comp]
    rw [← μ_natural_right_assoc, eraseDifferential_forget_tensor,
      eraseDifferential_forget_tensor_assoc, eraseDifferential_forget_map]
    exact μ_natural_right (U) M f
  associativity K L M := by
    apply (U).map_injective
    apply (cancel_epi ((μ (U) ((eraseDifferential A).obj K)
      ((eraseDifferential A).obj L) ▷ (U).obj ((eraseDifferential A).obj M)) ≫
        μ (U) ((eraseDifferential A).obj K ⊗ (eraseDifferential A).obj L)
          ((eraseDifferential A).obj M))).mp
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← μ_natural_left_assoc, ← comp_whiskerRight_assoc,
      eraseDifferential_forget_tensor, eraseDifferential_forget_tensor_assoc]
    rw [associativity_assoc (U) ((eraseDifferential A).obj K)
      ((eraseDifferential A).obj L) ((eraseDifferential A).obj M),
      ← μ_natural_right_assoc, ← whiskerLeft_comp_assoc,
      eraseDifferential_forget_tensor, eraseDifferential_forget_tensor,
      eraseDifferential_forget_map]
    exact associativity (U) K L M
  left_unitality K := by
    apply (U).map_injective
    apply (cancel_epi ((ε (U) ▷ (U).obj ((eraseDifferential A).obj K)) ≫
      μ (U) (𝟙_ (Complex A)) ((eraseDifferential A).obj K))).mp
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← μ_natural_left_assoc, ← comp_whiskerRight_assoc,
      eraseDifferential_forget_unit, eraseDifferential_forget_tensor_assoc,
      eraseDifferential_forget_map]
    rw [← left_unitality (U) ((eraseDifferential A).obj K)]
    exact left_unitality (U) K
  right_unitality K := by
    apply (U).map_injective
    apply (cancel_epi (((U).obj ((eraseDifferential A).obj K) ◁ ε (U)) ≫
      μ (U) ((eraseDifferential A).obj K) (𝟙_ (Complex A)))).mp
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← μ_natural_right_assoc, ← whiskerLeft_comp_assoc,
      eraseDifferential_forget_unit, eraseDifferential_forget_tensor_assoc,
      eraseDifferential_forget_map]
    rw [← right_unitality (U) ((eraseDifferential A).obj K)]
    exact right_unitality (U) K

/-- The inverse graded comparisons commute with erasing the differential. -/
@[reassoc]
lemma eraseDifferential_forget_tensor_delta (K L : Complex A) :
    (U).map (eraseDifferentialTensorIso A K L).hom ≫ δ (U) K L =
      δ (U) ((eraseDifferential A).obj K) ((eraseDifferential A).obj L) := by
  apply (cancel_epi (μ (U) ((eraseDifferential A).obj K)
    ((eraseDifferential A).obj L))).mp
  rw [eraseDifferential_forget_tensor_assoc, Functor.Monoidal.μ_δ,
    Functor.Monoidal.μ_δ]
  rfl

/-- 微分を消す操作は Koszul の対称性を保つ。 -/
instance eraseDifferential_laxBraided : (eraseDifferential A).LaxBraided where
  toLaxMonoidal := (eraseDifferentialCoreMonoidal A).toLaxMonoidal
  braided K L := by
    apply (U).map_injective
    change (U).map ((eraseDifferentialTensorIso A K L).hom ≫
      (eraseDifferential A).map (β_ K L).hom) =
        (U).map ((β_ ((eraseDifferential A).obj K) ((eraseDifferential A).obj L)).hom ≫
          (eraseDifferentialTensorIso A L K).hom)
    apply (cancel_epi (μ (U) ((eraseDifferential A).obj K)
      ((eraseDifferential A).obj L))).mp
    apply (cancel_mono (δ (U) L K)).mp
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [eraseDifferential_forget_tensor_assoc, eraseDifferential_forget_map,
      eraseDifferential_forget_tensor_delta]
    exact (eraseDifferential_forget_normalized_braiding A K L).symm

instance eraseDifferential_monoidal : (eraseDifferential A).Monoidal := by
  letI : IsIso (Functor.LaxMonoidal.ε (eraseDifferential A)) :=
    (eraseDifferentialUnitIso A).isIso_hom
  letI (K L : Complex A) : IsIso (Functor.LaxMonoidal.μ (eraseDifferential A) K L) :=
    (eraseDifferentialTensorIso A K L).isIso_hom
  exact Functor.Monoidal.ofLaxMonoidal _

end SerrePositivity.EInfinity
