module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomDiagramDegreePrecompose

/-!
# 元の Hom–Tot/BK 比較の任意次数合成の各行

概要：元の指定比較の合成は重み次数とHom次数のKoszul符号を持つ。
方針：指定行表示、Hom–Tot合成、自由Yoneda逆評価、同じ符号の計算を合成する。
規約：IS-W2 B02の同じ全パラメータ成分照合の分割。
使われ方：HA 1.2.4、実AW合成とtensor–Homの指定比較の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable {A : Type u} [CommRing A]

/-- 概要：指定Hom–Tot/BK比較の各行は任意次数合成を同じKoszul符号で保つ。
方針：元の行の式と逆評価の合成則を適用する。
規約：p・qは任意整数、nは元の重み次数。使われ方：HA 1.2.4 の全Hom単体の照合。 -/
theorem homToNormalizedBousfieldKan_rows_comp {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q : ℤ) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) (p + q)
      ((homToNormalizedBousfieldKan P X).f (p + q) (f.comp g rfl)) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))) q
        ((homToNormalizedBousfieldKan Q X).f q g) n ≫
      homDiagramDegreePrecompose X p (q - n) (p + q - n) (by omega) f) := by
  rw [homToNormalizedBousfieldKan_rows, homToNormalizedBousfieldKan_rows,
    homTotalComponent_homogeneous_comp]
  have he := freeUnitWeightEnd_inv_degree_precompose X p (q - n) (p + q - n)
    (by omega) f n (homTotalComponent Q X q n g)
  rw [← he]
  have hs : weightEndHomSign n (p + q) =
      ((n : ℤ) * p).negOnePow * weightEndHomSign n q := by
    unfold weightEndHomSign
    have h : (n : ℤ) * (p + q + 1) = (n : ℤ) * p + (n : ℤ) * (q + 1) := by ring
    rw [h, Int.negOnePow_add, mul_assoc]
  rw [hs, mul_smul]
  simp only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
