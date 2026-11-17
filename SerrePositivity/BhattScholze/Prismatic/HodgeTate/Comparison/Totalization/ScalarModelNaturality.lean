module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedScalarModels

/-!
# 指定された底変換模型の射との可換性

## 概要
指定 K-flat 分解の可換な四角形に対し、固定係数模型との比較は元の S 底変換の射を保つ。

## 方針
分解の擬同型との合成で正規化し、係数増大と係数制限の自然性を使う。

## 規約
存在する厳密な分解の射を入力とする。対象ごとの分解の存在から厳密な図式の存在を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の標準 S 線形比較の制限後の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (L : ScalarResolution f)

/-- 分解上の比較を導来係数制限へ渡した元の射。 -/
def derivedModelAugmentation (P : Complex R) :
    DerivedCategory.Q.obj (L.tensorFunctor.obj P) ⟶
      (derivedRestrictScalars f).obj (DerivedCategory.Q.obj (baseChange f P)) :=
  DerivedCategory.Q.map (L.comparison P) ≫
    ((derivedRestrictScalarsFactors f).app (baseChange f P)).inv

/-- 分解の擬同型との合成で、模型同型は元の係数増大に戻る。 -/
@[reassoc] theorem tensor_modelMap_comp_baseChangeModelIso
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    DerivedCategory.Q.map (L.tensorFunctor.map q) ≫ (L.baseChangeModelIso q hq hP).hom =
      L.derivedModelAugmentation P := by
  haveI := hq
  haveI := L.tensorFunctor_map_quasiIso q
  simp only [baseChangeModelIso, derivedModelAugmentation, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]

/-- 元の係数増大を導来係数制限へ渡しても、すべての鎖写像について自然である。 -/
@[reassoc] theorem derivedModelAugmentation_naturality {P Q : Complex R} (h : P ⟶ Q) :
    DerivedCategory.Q.map (L.tensorFunctor.map h) ≫ L.derivedModelAugmentation Q =
      L.derivedModelAugmentation P ≫ (derivedRestrictScalars f).map
        (DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) := by
  dsimp only [derivedModelAugmentation]
  rw [← Category.assoc, ← Functor.map_comp, comparison_naturality, Functor.map_comp,
    Category.assoc]
  have hn := (derivedRestrictScalarsFactors f).inv.naturality
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)
  simp only [Functor.comp_map] at hn
  simpa only [Category.assoc, Iso.app_inv] using
    congrArg (fun t => DerivedCategory.Q.map (L.comparison P) ≫ t) hn

/-- 指定した分解の可換な射は、元の S 線形底変換の同じ射へ移る。 -/
@[reassoc] theorem baseChangeModelIso_naturality
    {P Q K M : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P)
    (q' : Q ⟶ M) (hq' : QuasiIso q') (hQ : complexKFlat R Q)
    (g : K ⟶ M) (h : P ⟶ Q) (comm : q ≫ g = h ≫ q') :
    DerivedCategory.Q.map (L.tensorFunctor.map g) ≫ (L.baseChangeModelIso q' hq' hQ).hom =
      (L.baseChangeModelIso q hq hP).hom ≫ (derivedRestrictScalars f).map
        (DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) := by
  haveI := hq
  haveI := L.tensorFunctor_map_quasiIso q
  apply (cancel_epi (DerivedCategory.Q.map (L.tensorFunctor.map q))).mp
  have hc := congrArg (fun t => DerivedCategory.Q.map (L.tensorFunctor.map t)) comm
  simp only [Functor.map_comp] at hc
  calc
    _ = DerivedCategory.Q.map (L.tensorFunctor.map h) ≫
        (DerivedCategory.Q.map (L.tensorFunctor.map q') ≫ (L.baseChangeModelIso q' hq' hQ).hom) := by
      rw [← Category.assoc, hc, Category.assoc]
    _ = DerivedCategory.Q.map (L.tensorFunctor.map h) ≫ L.derivedModelAugmentation Q := by
      rw [tensor_modelMap_comp_baseChangeModelIso]
    _ = L.derivedModelAugmentation P ≫ (derivedRestrictScalars f).map
        (DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) :=
      L.derivedModelAugmentation_naturality h
    _ = _ := by rw [← Category.assoc, tensor_modelMap_comp_baseChangeModelIso]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
