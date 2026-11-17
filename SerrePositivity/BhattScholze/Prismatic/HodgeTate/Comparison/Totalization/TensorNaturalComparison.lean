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

private theorem extendedRows_hom_ext (K : CochainComplex (Complex R) ℕ)
    (M : CochainComplex (Complex R) ℤ)
    {f g : K.extend ComplexShape.embeddingUpNat ⟶ M}
    (h : ∀ n : ℕ, f.f (n : ℤ) = g.f (n : ℤ)) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : 0 ≤ i
  · lift i to ℕ using hi
    exact h i
  · exact (K.isZero_extend_X ComplexShape.embeddingUpNat i (fun n hn => by
      change (n : ℤ) = i at hn
      omega)).eq_of_src _ _

set_option maxHeartbeats 800000 in
-- 公開した延長射の型の正規化では、閉構造と零延長の同じ型を照合する。
/-- 非負行で延長した単位は、元の行の単位を指定行同型で挟んだ射である。 -/
theorem tensorUnitRowsNat_f_natCast (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (n : ℕ) :
    (tensorUnitRowsNat L K).f (n : ℤ) = (rowIso K n).hom ≫
      (ihom.adjunction L).unit.app (K.X n) ≫
        (homFunctor L).map (rowIso (tensorRows L K) n).inv := by
  change extendRowComponent K
    (((homFunctor L).mapHomologicalComplex (.up ℤ)).obj
      ((tensorRows L K).extend ComplexShape.embeddingUpNat))
    (fun m => (ihom.adjunction L).unit.app (K.X m) ≫
      (homFunctor L).map (rowIso (tensorRows L K) m).inv) (n : ℤ) = _
  exact extendRowComponent_natCast K _ _ n

/-- 指定行同型の逆は、零延長した図式の射と可換である。 -/
@[reassoc] theorem rowIso_inv_naturality {K M : CochainComplex (Complex R) ℕ}
    (g : K ⟶ M) (n : ℕ) :
    (rowIso K n).inv ≫ (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat).f (n : ℤ) =
      g.f n ≫ (rowIso M n).inv := by
  apply (cancel_mono (rowIso M n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rowIso_naturality, Iso.inv_hom_id_assoc]

/-- 元の非負横次数の図式について、延長した単位は自然である。 -/
@[reassoc] theorem tensorUnitRowsNat_naturality (L : Complex R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    HomologicalComplex.extendMap g ComplexShape.embeddingUpNat ≫ tensorUnitRowsNat L M =
      tensorUnitRowsNat L K ≫ ((homFunctor L).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap
          (((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).map g)
          ComplexShape.embeddingUpNat) := by
  apply extendedRows_hom_ext K
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [tensorUnitRowsNat_f_natCast, tensorUnitRowsNat_f_natCast]
  simp only [Category.assoc]
  rw [← Category.assoc, rowIso_naturality]
  simp only [Category.assoc]
  rw [← Functor.map_comp, rowIso_inv_naturality, Functor.map_comp]
  change (rowIso K n).hom ≫ g.f n ≫ (ihom.adjunction L).unit.app (M.X n) ≫
      (homFunctor L).map (rowIso (tensorRows L M) n).inv =
    (rowIso K n).hom ≫ (ihom.adjunction L).unit.app (K.X n) ≫
      (ihom L).map ((tensorLeft L).map (g.f n)) ≫
        (homFunctor L).map (rowIso (tensorRows L M) n).inv
  simpa only [Category.assoc, Functor.id_map, Functor.comp_map] using congrArg
    (fun h => (rowIso K n).hom ≫ h ≫
      (homFunctor L).map (rowIso (tensorRows L M) n).inv)
    ((ihom.adjunction L).unit.naturality (g.f n))

/-- 指定した非負模型の標準比較の転置は、図式について自然である。 -/
@[reassoc] theorem tensorTotalTransposeNat_naturality (L : Complex R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    (ProductTotal.functor (ModuleCat.{u} R)).map
        (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫ tensorTotalTransposeNat L M =
      tensorTotalTransposeNat L K ≫ homPostcompose L
        ((ProductTotal.functor (ModuleCat.{u} R)).map
          (HomologicalComplex.extendMap
            (((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).map g)
            ComplexShape.embeddingUpNat)) := by
  dsimp only [tensorTotalTransposeNat]
  rw [← Category.assoc, ← Functor.map_comp, tensorUnitRowsNat_naturality, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun h =>
    (ProductTotal.functor (ModuleCat.{u} R)).map (tensorUnitRowsNat L K) ≫ h)
      ((ProductTotal.homTotalNatIso L).inv.naturality
        (HomologicalComplex.extendMap
          (((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).map g)
          ComplexShape.embeddingUpNat))

/-- 指定した非負横次数の模型で、標準の比較鎖写像は自然である。 -/
@[reassoc] theorem tensorTotalComparison_naturality (L : Complex R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    cochainTensorMap (𝟙 L) ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) ≫
        tensorTotalComparison L M =
      tensorTotalComparison L K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).map g) := by
  apply (tensorHomEquiv L _ _).injective
  change tensorHomEquiv L _ _
    ((L ◁ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) ≫
      tensorTotalComparison L M) = _
  rw [tensorHomEquiv_naturality_source, tensorHomEquiv_naturality_target,
    tensorTotalComparison_transpose, tensorTotalComparison_transpose]
  exact tensorTotalTransposeNat_naturality L g

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
