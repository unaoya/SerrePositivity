module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorNaturalComparison

/-!
# 加法的関手と指定された零延長

## 概要
複体の加法的関手を各行へ施す操作と、非負横次数の零延長との指定同型を作る。

## 方針
非負行では元の行同型の像を使い、負の行では加法的関手が零対象を保つことを使う。

## 規約
前向き射は extendRowHom から構成する。同型の選択は元の行の同型で固定する。

## 使われ方
BS 著者版 Lemma 4.22 の Hom–Tot 比較と、元の非負横次数の模型の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 行ごとの関手と零延長を交換する、指定された前向き射。 -/
def extendFunctorComparison (F : Complex R ⥤ Complex R) [F.Additive]
    (K : CochainComplex (Complex R) ℕ) :
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) :=
  extendRowHom _ _ (fun n => F.map (rowIso K n).inv) (by
    intro n
    change F.map (rowIso K n).inv ≫
      F.map ((K.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)) =
        F.map (K.d n (n + 1)) ≫ F.map (rowIso K (n + 1)).inv
    rw [← Functor.map_comp, rowIso_inv_d, Functor.map_comp])

/-- 非負行での比較射は、元の指定された行同型の像である。 -/
theorem extendFunctorComparison_f_natCast (F : Complex R ⥤ Complex R) [F.Additive]
    (K : CochainComplex (Complex R) ℕ) (n : ℕ) :
    (extendFunctorComparison F K).f (n : ℤ) =
      (rowIso ((F.mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫ F.map (rowIso K n).inv := by
  change extendRowComponent ((F.mapHomologicalComplex (.up ℕ)).obj K)
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))
    (fun m => F.map (rowIso K m).inv) (n : ℤ) = _
  exact extendRowComponent_natCast ((F.mapHomologicalComplex (.up ℕ)).obj K)
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))
    (fun m => F.map (rowIso K m).inv) n

/-- 加法的関手と零延長を交換する指定射は同型である。 -/
instance extendFunctorComparison_isIso (F : Complex R ⥤ Complex R) [F.Additive]
    (K : CochainComplex (Complex R) ℕ) : IsIso (extendFunctorComparison F K) := by
  haveI (i : ℤ) : IsIso ((extendFunctorComparison F K).f i) := by
    by_cases hi : 0 ≤ i
    · lift i to ℕ using hi
      rw [extendFunctorComparison_f_natCast]
      infer_instance
    · have hS := negativeRow_isZero ((F.mapHomologicalComplex (.up ℕ)).obj K) i (by omega)
      have hT : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).X i) :=
        F.map_isZero (negativeRow_isZero K i (by omega))
      let e := hS.iso hT
      have he : (extendFunctorComparison F K).f i = e.hom := hS.eq_of_src _ _
      rw [he]
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 元の非負行を保つ、加法的関手と零延長の指定同型。 -/
def extendFunctorIso (F : Complex R ⥤ Complex R) [F.Additive]
    (K : CochainComplex (Complex R) ℕ) :
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) :=
  asIso (extendFunctorComparison F K)

/-- 非負横次数の同じ積全複体について、指定された Hom–Tot 同型。 -/
def homTotalIsoNat (P : Complex R) (K : CochainComplex (Complex R) ℕ) :
    homComplex R P (total K) ≅ total (((homFunctor P).mapHomologicalComplex (.up ℕ)).obj K) :=
  ProductTotal.homTotalIso P (K.extend ComplexShape.embeddingUpNat) ≪≫
    (ProductTotal.functor (ModuleCat.{u} R)).mapIso (extendFunctorIso (homFunctor P) K).symm

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
