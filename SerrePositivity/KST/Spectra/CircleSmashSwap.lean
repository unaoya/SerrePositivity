module

public import SerrePositivity.KST.Spectra.CircleSmashTriangles

/-!
概要：円の smash 積の変数交換は二つの相対三角形を交換する。
方針：正方形の商射上で対称性の自然性を計算する。
規約：共通の対角辺は交換で固定される。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二重 loop の交換の符号の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二つの円の smash の交換は正方形の座標交換から降りる。
方針：smash の商射での交換の式と対称性の自然性を使う。
規約：基礎単体集合の射の厳密な等式。
使われ方：Goerss–Jardine I §7。両三角形の交換の計算。 -/
@[reassoc]
theorem circleSmashSquareQuotient_swap :
    circleSmashSquareQuotient.{u} ≫
      (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
        PointedSimplicialSet.circle.{u}).right =
      (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ circleSmashSquareQuotient := by
  have h : (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u}).right ≫
        (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).right =
      (β_ PointedSimplicialSet.circle.{u}.right PointedSimplicialSet.circle.{u}.right).hom ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).right :=
    congrArg Under.Hom.right (PointedObject.smashQuotient_swap _ _)
  dsimp only [circleSmashSquareQuotient]
  erw [Category.assoc, h, ← Category.assoc, BraidedCategory.braiding_naturality,
    Category.assoc]

/-- 概要：smash の変数交換は上側の相対三角形を下側へ移す。
方針：相対三角形の商射上で正方形の交換の式を使う。
規約：ホーンを潰した同じ相対三角形からの射を比較する。
使われ方：Goerss–Jardine I §7。写像空間の pullback の二つの射影の交換。 -/
@[reassoc (attr := simp)]
theorem circleSmashUpper_swap :
    circleSmashUpper.{u} ≫ PointedObject.smashSwap PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} = circleSmashLower := by
  apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
  simp only [Under.comp_right, circleSmashUpper_quotient_assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ (circleSmashSquareQuotient ≫
    (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u}).right) = _
  erw [circleSmashSquareQuotient_swap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_swap]
  exact circleSmashLower_quotient.symm

/-- 概要：smash の変数交換は下側の相対三角形を上側へ移す。
方針：正方形の下側の三角形の交換を商射上で使う。
規約：交換を二度行うと元に戻る。
使われ方：Goerss–Jardine I §7。写像空間の二つの射影の交換の逆方向。 -/
@[reassoc (attr := simp)]
theorem circleSmashLower_swap :
    circleSmashLower.{u} ≫ PointedObject.smashSwap PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} = circleSmashUpper := by
  apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
  simp only [Under.comp_right, circleSmashLower_quotient_assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ (circleSmashSquareQuotient ≫
    (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u}).right) = _
  erw [circleSmashSquareQuotient_swap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_swap]
  exact circleSmashUpper_quotient.symm

end

end SerrePositivity.KST.Spectra
