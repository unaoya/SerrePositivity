module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComponents
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorCoefficientNaturality
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex

/-!
# 標準 S 線形比較と固定係数比較の零次数係数での照合

## 概要
S を R 加群として零次数に置いたテンソルの比較が、元の S 線形の標準比較に移ることを確認する。

## 方針
元の指定行射影と同次テンソルで比較する。係数の非零次数は零対象であり、零次数の交換符号は一である。

## 規約
比較の一致を仮定せず、元の係数制限の同型と元の随伴から計算する。

## 使われ方
BS 著者版 Lemma 4.22 の係数分解の増大と標準 S 線形比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 係数制限の指定同型の順向きも、元の指定行成分を保つ。 -/
@[reassoc] theorem restrictionTotalIso_hom_π (f : R →+* S)
    (K : CochainComplex (Complex S) ℕ) (q : ℤ) (n : ℕ) :
    (restrictionTotalIso f K).hom.f q ≫ componentπ (restrictedRows f K) n q =
      (ModuleCat.restrictScalars f).map (componentπ K n q) := restrictionTotalDegree_π f K q n

/-- 通常の各行の底変換を制限すると、同じ零次数係数との行テンソルになる。 -/
def restrictedBaseChangeRowsIso (f : R →+* S) (K : CochainComplex (Complex R) ℕ) :
    restrictedRows f ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
      (.up ℕ)).obj K) ≅ tensorRows (cochainSingleZero (baseChangeScalarModule f)) K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => restrictedBaseChangeComplexIso f (K.X n))
    (by intro i j _; exact (restrictedBaseChangeComplexIso_naturality f (K.d i j)).symm)

/-- 零次数係数の元の同次テンソルを、通常の係数拡大へ戻す公式。 -/
@[reassoc] theorem ι_restrictedBaseChangeComplexIso_inv (f : R →+* S) (P : Complex R) (q : ℤ) :
    ιTensorObj (cochainSingleZero (baseChangeScalarModule f)) P 0 q q (zero_add q) ≫
        (restrictedBaseChangeComplexIso f P).inv.f q =
      ((singleObjXSelf (.up ℤ) 0 (baseChangeScalarModule f)).hom ▷ P.X q) ≫
        (extendRestrictTensorIso f).inv.app (P.X q) := by
  simp only [restrictedBaseChangeComplexIso, Iso.trans_inv, Iso.symm_inv, HomologicalComplex.comp_f]
  change ιTensorObj (cochainSingleZero (baseChangeScalarModule f)) P 0 q q (zero_add q) ≫
      (tensorSingleLeftDesc (baseChangeScalarModule f) P q ≫ (extendRestrictTensorIso f).inv.app (P.X q)) = _
  rw [ι_tensorSingleLeftDesc_assoc]

/-- 零次数係数の標準テンソル比較は、元の S 線形標準比較を係数制限した射そのものである。 -/
theorem scalarSingle_totalComparison_compatibility (f : R →+* S)
    (K : CochainComplex (Complex R) ℕ) :
    (restrictedBaseChangeComplexIso f (total K)).inv ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map (baseChangeTotalComparison f K) ≫
        (restrictionTotalIso f ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
          (.up ℕ)).obj K)).hom =
      tensorTotalComparison (cochainSingleZero (baseChangeScalarModule f)) K ≫
        (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (restrictedBaseChangeRowsIso f K).inv := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f]
  apply mapBifunctor.hom_ext
  intro a b hab
  change a+b=q at hab
  by_cases ha : a=0
  · subst a
    have hb : b=q := by omega
    subst b
    apply component_hom_ext
    intro n
    simp only [Category.assoc, tensorTotalComparison_f_eq, Functor.mapHomologicalComplex_map_f]
    rw [restrictionTotalIso_hom_π, ← Functor.map_comp, baseChangeTotalComparison_component,
      componentπ_naturality, tensorComparisonDegree_component_assoc]
    dsimp only [tensorComponent]
    simp only [interchangeSign, zero_mul, Int.negOnePow_zero, one_smul]
    change ιTensorObj (cochainSingleZero (baseChangeScalarModule f)) (total K) 0 q q (zero_add q) ≫
        (restrictedBaseChangeComplexIso f (total K)).inv.f q ≫
          (ModuleCat.restrictScalars f).map ((ModuleCat.extendScalars f).map (componentπ K n q)) =
      (cochainSingleZero (baseChangeScalarModule f)).X 0 ◁ componentπ K n q ≫
        ιTensorObj (cochainSingleZero (baseChangeScalarModule f)) (K.X n) 0 (q-n) (q-n) (zero_add _) ≫
          (restrictedBaseChangeComplexIso f (K.X n)).inv.f (q-n)
    rw [ι_restrictedBaseChangeComplexIso_inv_assoc, ι_restrictedBaseChangeComplexIso_inv]
    have hn := (extendRestrictTensorIso f).inv.naturality (componentπ K n q)
    change (baseChangeScalarModule f ◁ componentπ K n q) ≫
        (extendRestrictTensorIso f).inv.app ((K.X n).X (q-n)) =
      (extendRestrictTensorIso f).inv.app ((total K).X q) ≫
        (ModuleCat.restrictScalars f).map ((ModuleCat.extendScalars f).map (componentπ K n q)) at hn
    rw [← hn, whisker_exchange_assoc]
  · exact ((tensorRight ((total K).X b)).map_isZero
      (isZero_single_obj_X (.up ℤ) 0 (baseChangeScalarModule f) a ha)).eq_of_src _ _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
