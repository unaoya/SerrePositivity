module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorHomComponents

/-!
# 標準テンソル–Tot 鎖写像の同次成分

## 概要
随伴から構成した標準比較を、元の同次テンソルと指定行射影で評価する。

## 方針
転置の評価と行の単位の評価を合わせ、二つの符号を横次数の交換符号へまとめる。

## 規約
鎖写像性を仮定した別の比較射を導入しない。同じ随伴からの鎖写像を計算する。

## 使われ方
BS 著者版 Lemma 4.22 の標準比較と、最初の次数成分の公式との同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped TensorProduct SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 随伴で作った鎖写像の指定成分は、横次数との交換符号を持つ通常のテンソル射である。 -/
theorem tensorTotalComparisonInt_component (L : Complex R) (K : CochainComplex (Complex R) ℤ)
    (a b q : ℤ) (hab : a + b = q) (n : ℤ)
    (x : ((ProductTotal.functor (ModuleCat.{u} R)).obj K).X b) (y : L.X a) :
    ProductTotal.π (tensorRowsInt L K) n (q - n) q (by omega)
        ((tensorTotalComparisonInt L K).f q
          (ιTensorObj L ((ProductTotal.functor (ModuleCat.{u} R)).obj K) a b q hab (y ⊗ₜ[R] x))) =
      (a * n).negOnePow • ιTensorObj L (K.X n) a (b - n) (q - n) (by omega)
        (y ⊗ₜ[R] ProductTotal.π K n (b - n) b (by omega) x) := by
  let D := tensorRowsInt L K
  let z := ((ProductTotal.functor (ModuleCat.{u} R)).map (tensorUnitRows L K)).f b x
  have hm := congrArg (fun f => f x)
    (ProductTotal.map_π (tensorUnitRows L K) n (b - n) b (by omega))
  simp only [ModuleCat.comp_apply] at hm
  change ProductTotal.π (((homFunctor L).mapHomologicalComplex (.up ℤ)).obj D)
      n (b - n) b (by omega) z =
    ((ihom.adjunction L).unit.app (K.X n)).f (b - n)
      (ProductTotal.π K n (b - n) b (by omega) x) at hm
  have hi := congrArg (fun f => f y)
    (homTotalInverse_component L D b z a q hab n (q - n) (by omega))
  simp only [ModuleCat.comp_apply] at hi
  rw [hm] at hi
  erw [tensorUnit_component L (K.X n) (b-n) a (q-n) (by omega)
    (ProductTotal.π K n (b-n) b (by omega) x) y] at hi
  change ProductTotal.π D n (q - n) q (by omega)
      (((tensorTotalTranspose L K).f b x).v a q hab y) = _ at hi
  have ht := tensorHomEquiv_component L
    ((ProductTotal.functor (ModuleCat.{u} R)).obj K)
    ((ProductTotal.functor (ModuleCat.{u} R)).obj D)
    (tensorTotalComparisonInt L K) b a q hab x y
  rw [tensorTotalComparisonInt_transpose] at ht
  have h := congrArg (fun t => ProductTotal.π D n (q - n) q (by omega) t) ht
  simp only [Units.smul_def, map_zsmul] at h
  change ProductTotal.π D n (q - n) q (by omega)
      (((tensorTotalTranspose L K).f b x).v a q hab y) =
    (b * a).negOnePow • ProductTotal.π D n (q - n) q (by omega)
      ((tensorTotalComparisonInt L K).f q
        (ιTensorObj L ((ProductTotal.functor (ModuleCat.{u} R)).obj K) a b q hab (y ⊗ₜ[R] x))) at h
  rw [hi] at h
  have hh := congrArg (fun v => (b * a).negOnePow • v) h
  simp only [smul_smul, Int.units_mul_self, one_smul] at hh
  rw [tensorTranspose_unit_sign] at hh
  exact hh.symm

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
