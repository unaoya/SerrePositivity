module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorAdjointComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ExtensionRows

/-!
# 非負横次数の標準テンソル–積全複体比較

## 概要
随伴の単位を元の非負横次数の図式で取り、指定された零延長からの射へ延長する。

## 方針
行同型の逆と随伴の単位を合成し、既存の Hom–Tot 同型を用いて逆転置する。

## 規約
始域・終域は最初に固定した cochainProductTotalizationFunctor の値である。
比較射の擬同型性は、この構成には仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の完備化前の標準比較鎖写像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 指定された零延長の行同型の逆は、元の横微分を保つ。 -/
theorem rowIso_inv_d (K : CochainComplex (Complex R) ℕ) (n : ℕ) :
    (rowIso K n).inv ≫
        (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      K.d n (n + 1) ≫ (rowIso K (n + 1)).inv := by
  apply (cancel_mono (rowIso K (n + 1)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rowIso_d, Iso.inv_hom_id_assoc]

/-- 非負行で指定した単位を、元の図式の零延長からの鎖写像へ延長する。 -/
def tensorUnitRowsNat (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    K.extend ComplexShape.embeddingUpNat ⟶
      ((homFunctor L).mapHomologicalComplex (.up ℤ)).obj
        ((tensorRows L K).extend ComplexShape.embeddingUpNat) :=
  extendRowHom K _
    (fun n => (ihom.adjunction L).unit.app (K.X n) ≫
      (homFunctor L).map (rowIso (tensorRows L K) n).inv)
    (by
      intro n
      change ((ihom.adjunction L).unit.app (K.X n) ≫
        (homFunctor L).map (rowIso (tensorRows L K) n).inv) ≫
          (homFunctor L).map (((tensorRows L K).extend ComplexShape.embeddingUpNat).d
            (n : ℤ) ((n + 1 : ℕ) : ℤ)) = _
      rw [Category.assoc, ← Functor.map_comp, rowIso_inv_d, Functor.map_comp]
      rw [← Category.assoc]
      exact congrArg (fun h => h ≫
        (homFunctor L).map (rowIso (tensorRows L K) (n + 1)).inv)
          ((ihom.adjunction L).unit.naturality (K.d n (n + 1))).symm)

/-- 指定した非負横次数の模型における、標準比較の転置。 -/
def tensorTotalTransposeNat (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    total K ⟶ homComplex R L (total (tensorRows L K)) :=
  (ProductTotal.functor (ModuleCat.{u} R)).map (tensorUnitRowsNat L K) ≫
    (ProductTotal.homTotalIso L ((tensorRows L K).extend ComplexShape.embeddingUpNat)).inv

/-- 同じ積全複体模型を始域・終域に持つ、標準のテンソル–Tot 鎖写像。 -/
def tensorTotalComparison (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    cochainTensor L (total K) ⟶ total (tensorRows L K) :=
  (tensorHomEquiv L _ _).symm (tensorTotalTransposeNat L K)

/-- この鎖写像の転置は、指定した行の単位と Hom–Tot の同型による射である。 -/
theorem tensorTotalComparison_transpose (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    tensorHomEquiv L _ _ (tensorTotalComparison L K) = tensorTotalTransposeNat L K :=
  Equiv.apply_symm_apply _ _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
