module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorUnitors
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductModel

/-!
# 二項余積から Hopf テンソルへの指定比較

## 概要
HA 3.2.4.7 の二つの包含を、BF §1.1.4 の単位代数と左右の単位同型から作る。

## 方針
単位代数の始対象性で単位射を選び、テンソルの全射での自然性から比較を自然変換にする。

## 規約
零入力の余単位の同型性だけを要求し、cofibrancy と擬同型性は別に証明する。

## 使われ方
自由代数の二色比較、セル対への移送、固定右因子ごとの全関手比較の順方向の射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory Limits
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- HA 3.2.4.7 の単位射は任意の代数射に沿って自然。 -/
lemma hopfTensorUnitMap_naturality (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0)))
    {Y Y' : P.Algebra} (g : Y ⟶ Y') :
    hopfTensorUnitMap hP h0 Y ≫ g = hopfTensorUnitMap hP h0 Y' :=
  (hopfTensorUnitIsInitial hP h0).hom_ext _ _

/-- HA 3.2.4.7 のテンソルへの第一の指定包含。 -/
def hopfTensorInl (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (X Y : P.Algebra) :
    X ⟶ hopfTensorAlgebra hP X Y :=
  (hopfTensorRightUnitor hP X).inv ≫ hopfTensorMap hP (𝟙 X) (hopfTensorUnitMap hP h0 Y)

/-- HA 3.2.4.7 のテンソルへの第二の指定包含。 -/
def hopfTensorInr (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (X Y : P.Algebra) :
    Y ⟶ hopfTensorAlgebra hP X Y :=
  (hopfTensorLeftUnitor hP Y).inv ≫ hopfTensorMap hP (hopfTensorUnitMap hP h0 X) (𝟙 Y)

/-- HA 3.2.4.7 の第一の包含は両変数の全射で自然。 -/
lemma hopfTensorInl_naturality (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0)))
    {X Y X' Y' : P.Algebra} (f : X ⟶ X') (g : Y ⟶ Y') :
    f ≫ hopfTensorInl hP h0 X' Y' = hopfTensorInl hP h0 X Y ≫ hopfTensorMap hP f g := by
  have hu := congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom (hopfTensorUnitMap_naturality hP h0 g)
  change (hopfTensorUnitMap hP h0 Y).hom ≫ g.hom = (hopfTensorUnitMap hP h0 Y').hom at hu
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  change f.hom ≫ (ρ_ X'.carrier).inv ≫ (𝟙 X'.carrier ⊗ₘ (hopfTensorUnitMap hP h0 Y').hom) =
    ((ρ_ X.carrier).inv ≫ (𝟙 X.carrier ⊗ₘ (hopfTensorUnitMap hP h0 Y).hom)) ≫
      (f.hom ⊗ₘ g.hom)
  simp only [Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, whiskerRight_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hu]

/-- HA 3.2.4.7 の第二の包含は両変数の全射で自然。 -/
lemma hopfTensorInr_naturality (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0)))
    {X Y X' Y' : P.Algebra} (f : X ⟶ X') (g : Y ⟶ Y') :
    g ≫ hopfTensorInr hP h0 X' Y' = hopfTensorInr hP h0 X Y ≫ hopfTensorMap hP f g := by
  have hu := congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom (hopfTensorUnitMap_naturality hP h0 f)
  change (hopfTensorUnitMap hP h0 X).hom ≫ f.hom = (hopfTensorUnitMap hP h0 X').hom at hu
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  change g.hom ≫ (λ_ Y'.carrier).inv ≫ ((hopfTensorUnitMap hP h0 X').hom ⊗ₘ 𝟙 Y'.carrier) =
    ((λ_ Y.carrier).inv ≫ ((hopfTensorUnitMap hP h0 X).hom ⊗ₘ 𝟙 Y.carrier)) ≫
      (f.hom ⊗ₘ g.hom)
  simp only [Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whiskerLeft_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hu]

/-- HA 3.2.4.7 の厳密な余積から、指定した二包含で作るテンソルへの比較。 -/
def hopfCoproductComparison (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (X Y : P.Algebra) :
    X ⨿ Y ⟶ hopfTensorAlgebra hP X Y :=
  coprod.desc (hopfTensorInl hP h0 X Y) (hopfTensorInr hP h0 X Y)

/-- HA 3.2.4.7 の全関手版で降ろす、固定右因子ごとの指定された自然変換。 -/
def hopfCoproductTensorNat (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (Y : P.Algebra) :
    modelCoprodWith Y ⟶ hopfTensorWith hP Y where
  app X := hopfCoproductComparison hP h0 X Y
  naturality {X X'} f := by
    change coprod.map f (𝟙 Y) ≫ hopfCoproductComparison hP h0 X' Y =
      hopfCoproductComparison hP h0 X Y ≫ hopfTensorMap hP f (𝟙 Y)
    apply coprod.hom_ext
    · simpa only [hopfCoproductComparison, coprod.inl_map_assoc,
        coprod.inl_desc, coprod.inl_desc_assoc] using hopfTensorInl_naturality hP h0 f (𝟙 Y)
    · simpa only [hopfCoproductComparison, coprod.inr_map_assoc,
        coprod.inr_desc, coprod.inr_desc_assoc, Category.id_comp] using
        hopfTensorInr_naturality hP h0 f (𝟙 Y)

-- 単位対象を A[0] へ展開して、模型の零入力の増大を照合する。
attribute [local semireducible] HomologicalComplex.monoidalCategoryStruct

namespace BarrattEccles
variable (R : Type u) [CommRing R]

/-- HA 3.2.4.7 の指定比較を、追加仮定なしに実際の Barratt–Eccles 模型へ適用する。 -/
def barrattEcclesCoproductTensorNat (Y : (operad R).Algebra) :
    modelCoprodWith Y ⟶ hopfTensorWith (hopf R) Y := by
  have h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0)) := by
    change IsIso ((augmentation R).map.app (FiniteBijection.of 0))
    rw [augmentation_app]
    exact zeroArity_augmentation_isIso R
  exact hopfCoproductTensorNat (hopf R) h0 Y

end BarrattEccles

end SerrePositivity.EInfinity
