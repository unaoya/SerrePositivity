module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorNatComponents

/-!
# 標準テンソル–Tot 比較の係数についての自然性

## 概要
固定係数複体の鎖写像に対しても、同じ標準比較の四角形は可換である。

## 方針
元の指定行成分と同次テンソル上で比較し、同じ交換符号を使う。

## 規約
係数複体に新しい環作用を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の係数分解の増大と標準 S 底変換の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped TensorProduct

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 元の係数鎖写像を各行へ施す射。 -/
def tensorRowsCoefficientMap {L M : Complex R} (h : L ⟶ M)
    (K : CochainComplex (Complex R) ℕ) : tensorRows L K ⟶ tensorRows M K where
  f n := cochainTensorMap h (𝟙 (K.X n))
  comm' i j _ := by
    change cochainTensorMap h (𝟙 (K.X i)) ≫ cochainTensorMap (𝟙 M) (K.d i j) =
      cochainTensorMap (𝟙 L) (K.d i j) ≫ cochainTensorMap h (𝟙 (K.X j))
    simp only [cochainTensorMap_comp, Category.comp_id, Category.id_comp]

/-- 元の標準比較は係数複体の鎖写像についても自然である。 -/
@[reassoc] theorem tensorTotalComparison_coefficient_naturality
    {L M : Complex R} (h : L ⟶ M) (K : CochainComplex (Complex R) ℕ) :
    cochainTensorMap h (𝟙 (total K)) ≫ tensorTotalComparison M K =
      tensorTotalComparison L K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (tensorRowsCoefficientMap h K) := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, tensorTotalComparison_f_eq]
  apply mapBifunctor.hom_ext
  intro a b hab
  change a+b=q at hab
  apply component_hom_ext
  intro n
  simp only [Category.assoc]
  rw [ιTensorObj_cochainTensorMap_assoc, tensorComparisonDegree_component,
    componentπ_naturality]
  rw [tensorComparisonDegree_component_assoc]
  dsimp only [tensorRowsCoefficientMap, tensorComponent]
  rw [Linear.comp_units_smul, Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [ιTensorObj_cochainTensorMap]
  simp only [HomologicalComplex.id_f, tensorHom_id]
  rw [whisker_exchange_assoc]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
