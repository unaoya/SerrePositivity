module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 可換 dg オペラッド

概要：Berger–Moerdijk §1 の可換オペラッド Com を整数コチェイン複体上に構成する。
方針：全 arity をテンソル単位 A[0] とし、単位子を部分合成とする。
規約：全ての対称群作用は恒等射である。
使われ方：Barratt–Eccles オペラッドの augmentation の終域となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：各 arity の複体が A[0] である可換オペラッド（Berger–Moerdijk §1）。
方針：定数の対称列とテンソル単位の単位子を用い、モノイダル整合性で法則を示す。
規約：arity 0 を含み、作用は自明とする。
使われ方：可換 A 代数を dg オペラッドの代数として扱う。 -/
def commutativeOperad : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A where
  sequence := (Functor.const _root_.SerrePositivity.FiniteBijection).obj (𝟙_ (Complex A))
  unit := 𝟙 _
  comp _ _ _ := (λ_ (𝟙_ (Complex A))).hom
  unit_comp n := by
    change (𝟙 (𝟙_ (Complex A)) ▷ 𝟙_ (Complex A)) ≫ (λ_ (𝟙_ (Complex A))).hom ≫
      𝟙 _ = (λ_ (𝟙_ (Complex A))).hom
    simp
  comp_unit m i := by
    change (𝟙_ (Complex A) ◁ 𝟙 (𝟙_ (Complex A))) ≫ (λ_ (𝟙_ (Complex A))).hom =
      (ρ_ (𝟙_ (Complex A))).hom
    simp [unitors_equal]
  inner_equivariance m n i σ := by
    change (𝟙_ (Complex A) ◁ 𝟙 (𝟙_ (Complex A))) ≫ (λ_ (𝟙_ (Complex A))).hom =
      (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 _
    simp
  outer_equivariance m n i σ := by
    change (𝟙 (𝟙_ (Complex A)) ▷ 𝟙_ (Complex A)) ≫ (λ_ (𝟙_ (Complex A))).hom =
      (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 _
    simp
  nested_assoc m n k i j := by
    change ((λ_ (𝟙_ (Complex A))).hom ▷ 𝟙_ (Complex A)) ≫ (λ_ (𝟙_ (Complex A))).hom =
      (α_ (𝟙_ (Complex A)) (𝟙_ (Complex A)) (𝟙_ (Complex A))).hom ≫
        (𝟙_ (Complex A) ◁ (λ_ (𝟙_ (Complex A))).hom) ≫ (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 _
    monoidal_coherence
  parallel_assoc m n k i j hij := by
    change ((λ_ (𝟙_ (Complex A))).hom ▷ 𝟙_ (Complex A)) ≫ 𝟙 _ ≫
        (λ_ (𝟙_ (Complex A))).hom =
      (α_ (𝟙_ (Complex A)) (𝟙_ (Complex A)) (𝟙_ (Complex A))).hom ≫
        (𝟙_ (Complex A) ◁ (β_ (𝟙_ (Complex A)) (𝟙_ (Complex A))).hom) ≫
        (α_ (𝟙_ (Complex A)) (𝟙_ (Complex A)) (𝟙_ (Complex A))).inv ≫
        ((λ_ (𝟙_ (Complex A))).hom ▷ 𝟙_ (Complex A)) ≫ 𝟙 _ ≫
        (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 _
    rw [braiding_tensorUnit_left]
    monoidal_coherence

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
