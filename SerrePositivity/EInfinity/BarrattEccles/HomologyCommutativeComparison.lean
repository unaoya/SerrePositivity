module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyOperations
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraRestriction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebra

/-!
# 可換モノイド複体を制限した E 代数の H⁰ 演算

概要：BF §1・BM §1 の E → Com の制限では、選んだ演算は元の積と単位そのものになる。
方針：係数の切断と augmentation の合成を恒等射へ簡約する。
規約：複体射の厳密な等式で、ホモロジーの同型だけには留めない。
使われ方：離散可換代数の H⁰ の積・単位の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] (X : Complex A) [MonObj X] [IsCommMonObj X]

/-- 概要：Com から制限した E 代数の零次演算は元の全反復積（BF §1、BM §1）。
方針：切断と augmentation の合成、単位子の逆と正の合成を相殺する。
規約：零入力も含む全 arity。
使われ方：H⁰ の演算を通常の可換代数の演算と比較する。 -/
lemma homologyOperation_commutative (n : ℕ) :
    homologyOperation (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj (augmentation A)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X)) n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n := by
  change (λ_ (power X n)).inv ≫ (aritySection A n ▷ power X n) ≫
    ((augmentation A).map.app (FiniteBijection.of n) ▷ power X n) ≫
    (λ_ (power X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n = _
  rw [← comp_whiskerRight_assoc, aritySection_augmentation, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc]

/-- 概要：Com から制限した E 代数の二入力射は元の二項積（BF §1、BM §1）。
方針：二入力の反復積に残る単位因子を一入力比較で相殺する。
規約：実際の複体射としての等式。
使われ方：離散 E 代数の H⁰ の積が元の積を与えることの比較。 -/
lemma homologyBinary_commutative :
    homologyBinary (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj (augmentation A)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X)) = μ[X] := by
  rw [homologyBinary, homologyOperation_commutative]
  change (X ◁ (oneIso X).inv) ≫ (X ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X 1) ≫ μ[X] = μ[X]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_one, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    whiskerLeft_id, Category.id_comp]

/-- 概要：Com から制限した E 代数の零入力射は元の単位（BF §1、BM §1）。
方針：全反復積の零入力公式を適用する。
規約：実際の nullary 演算。
使われ方：離散 E 代数の H⁰ の単位の比較。 -/
lemma homologyNullary_commutative :
    homologyOperation (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj (augmentation A)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X)) 0 = η[X] :=
  homologyOperation_commutative X 0

end SerrePositivity.EInfinity.BarrattEccles
