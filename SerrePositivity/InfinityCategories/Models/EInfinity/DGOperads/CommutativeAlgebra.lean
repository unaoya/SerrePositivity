module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Commutative
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativePowers
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MonoidInsertionAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MonoidMaps

/-!
模型。文献の定義との比較は後で
# 可換モノイド複体から Com の代数へ

概要：BM §1 の Com 代数を、実際の複体上の可換モノイド対象から構成する。
方針：反復積を全 arity の作用とし、置換不変性と代入の積の公式を使う。
規約：空積はモノイド対象の単位、arity 零を含む。
使われ方：離散可換代数を E → Com に沿って E 代数にする。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：可換モノイド複体の全反復積は Com の代数構造（BM §1）。
方針：単位・置換・部分合成の三公理を反復積の一般公式から得る。
規約：底の複体はそのまま、arity 零を含む。
使われ方：離散可換代数の Com 構造と E への制限。 -/
def commutativeAlgebraOfMonoid (X : Complex A) [MonObj X] [IsCommMonObj X] :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A).Algebra where
  carrier := X
  action n := (λ_ (power X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n
  equivariance n σ := by
    change (𝟙 (𝟙_ (Complex A)) ⊗ₘ (permutationAction X n σ).asIso.hom) ≫
      ((λ_ (power X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n) = _
    rw [id_tensorHom, leftUnitor_naturality_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_permutation]
  unit_action := by
    change (𝟙 (𝟙_ (Complex A)) ▷ power X 1) ≫
      ((λ_ (power X 1)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X 1) = _
    rw [id_whiskerRight, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_one]
  comp_action m n i := by
    change ((λ_ (𝟙_ (Complex A))).hom ▷ power X (m + n)) ≫
      ((λ_ (power X (m + n))).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (m + n)) =
      (α_ (𝟙_ (Complex A)) (𝟙_ (Complex A)) (power X (m + n))).hom ≫
        ((𝟙_ (Complex A)) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (𝟙_ (Complex A)) m n i
          ((λ_ (power X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n)) ≫
        ((λ_ (power X (m + 1))).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (m + 1))
    rw [leftUnitor_naturality_assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_insertion]
    monoidal

/-- 概要：モノイド複体の射は全入力の Com 作用を保つ（BM §1）。
方針：単位子の自然性と反復積の射保存を使う。
規約：射の底は元の複体射そのもの。
使われ方：離散可換代数の射を Com 代数射にする。 -/
def commutativeAlgebraMap {X Y : Complex A} [MonObj X] [MonObj Y]
    [IsCommMonObj X] [IsCommMonObj Y] (f : X ⟶ Y) [IsMonHom f] :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid Y where
  hom := f
  comm n := by
    change ((λ_ (power X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n) ≫ f =
      (𝟙 (𝟙_ (Complex A)) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f n) ≫
        ((λ_ (power Y n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct Y n)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_map, id_tensorHom, leftUnitor_naturality_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
