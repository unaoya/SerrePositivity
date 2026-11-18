module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorAlgebra
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorNaturality

/-!
# Hopf テンソル代数の関手

## 概要
BF §1.1.4 のテンソル代数を、HA 3.2.4.7 の全関手比較に使う二変数の関手にする。

## 方針
元の二つの代数射のテンソルが作用を保つことを使い、台のテンソルの関手則を移す。

## 規約
右因子を固定した関手も同じ射を使い、cofibrancy と弱同値性はここでは仮定しない。

## 使われ方
二項余積からテンソルへの指定された比較の自然性と、局所化への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- BF §1.1.4 の二つの代数射のテンソルは、テンソル代数の射を与える。 -/
def hopfTensorMap (hP : P.Hopf) {X Y X' Y' : P.Algebra} (f : X ⟶ X') (g : Y ⟶ Y') :
    hopfTensorAlgebra hP X Y ⟶ hopfTensorAlgebra hP X' Y' where
  hom := f.hom ⊗ₘ g.hom
  comm n := hopfTensorAction_naturality hP f g n

/-- BF §1.1.4 のテンソル代数は二変数の関手をなす。 -/
def hopfTensorFunctor (hP : P.Hopf) : P.Algebra × P.Algebra ⥤ P.Algebra where
  obj X := hopfTensorAlgebra hP X.1 X.2
  map f := hopfTensorMap hP f.1 f.2
  map_id X := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change (𝟙 X.1.carrier ⊗ₘ 𝟙 X.2.carrier) = 𝟙 _
    rw [tensorHom_id, id_whiskerRight]
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change ((f.1.hom ≫ g.1.hom) ⊗ₘ (f.2.hom ≫ g.2.hom)) =
      (f.1.hom ⊗ₘ f.2.hom) ≫ (g.1.hom ⊗ₘ g.2.hom)
    rw [tensorHom_comp_tensorHom]

/-- HA 3.2.4.7 の強い比較で使う、右因子を固定した厳密テンソル関手。 -/
def hopfTensorWith (hP : P.Hopf) (Y : P.Algebra) : P.Algebra ⥤ P.Algebra where
  obj X := hopfTensorAlgebra hP X Y
  map f := hopfTensorMap hP f (𝟙 Y)
  map_id X := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change (𝟙 X.carrier ⊗ₘ 𝟙 Y.carrier) = 𝟙 _
    rw [tensorHom_id, id_whiskerRight]
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change ((f.hom ≫ g.hom) ⊗ₘ 𝟙 Y.carrier) =
      (f.hom ⊗ₘ 𝟙 Y.carrier) ≫ (g.hom ⊗ₘ 𝟙 Y.carrier)
    rw [tensorHom_comp_tensorHom, Category.id_comp]

end SerrePositivity.EInfinity
