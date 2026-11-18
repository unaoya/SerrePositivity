module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeBinaryCriterion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebra

/-!
模型。文献の定義との比較は後で
# 可換モノイドの Com 代数の元の単位と積

概要：Com 化の通常の零入力・二入力は元のモノイド演算。
方針：係数単位子と一入力冪の単位子を相殺する。
規約：元の底と演算の厳密な等式。
使われ方：離散可換代数への標準 H⁰ 同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X : Complex A) [MonObj X] [IsCommMonObj X]
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

lemma commutativeUnit_ofMonoid :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeUnit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X) = η[X] := by
  change (λ_ (power X 0)).inv ≫ (λ_ (power X 0)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X 0 = _
  rw [Iso.inv_hom_id_assoc]
  rfl

lemma commutativeBinary_ofMonoid :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeBinary (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X) = μ[X] := by
  change (X ◁ (oneIso X).inv) ≫ (λ_ (power X 2)).inv ≫
    (λ_ (power X 2)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X 2 = _
  rw [Iso.inv_hom_id_assoc]
  change (X ◁ (oneIso X).inv) ≫ (X ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X 1) ≫ μ[X] = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_one, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    whiskerLeft_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
