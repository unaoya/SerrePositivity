module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.StandardCompletedModelNaturality

/-!
# 元の導来比較と指定模型の射

## 概要
標準の導来源の計算同型と S 完備比較が、実際の可換な模型の射を保つ。

## 方針
既存の導来係数拡大の増大と反復完備化の比較自然同型を使う。

## 規約
模型の射の存在や可換性を仮定したことにせず、実際の射とその等式を渡す。

## 使われ方
BS 著者版 Lemma 4.22 の模型間の照合と元の比較射の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.DifferentialGraded.ScalarExtension
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の完備導来源の模型同型は、指定模型の実際の射について自然である。 -/
@[reassoc] theorem nativeCompletedScalarModelIso_naturality (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {P Q K M : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P)
    (q' : Q ⟶ M) (hq' : QuasiIso q') (hQ : complexKFlat R Q)
    (g : K ⟶ M) (h : P ⟶ Q) (comm : q ≫ g = h ≫ q') :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).map
        ((complexDerivedExtension f).map (DerivedCategory.Q.map g)) ≫
          (nativeCompletedScalarModelIso f x q' hq' hQ).hom =
      (nativeCompletedScalarModelIso f x q hq hP).hom ≫
        DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) := by
  dsimp only [nativeCompletedScalarModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, nativeDerivedScalarModelIso_naturality f q hq hP q' hq' hQ g h comm,
    Functor.map_comp, Category.assoc]
  have hn := (finiteDerivedCompletionComparison (fun j => f (x j))).hom.naturality
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)
  simp only [Functor.comp_map] at hn
  simpa only [Category.assoc, Functor.comp_obj, baseChange, Iso.app_hom] using congrArg
    (fun k => (finiteDerivedCompletionFunctor (fun j => f (x j))).map
      (nativeDerivedScalarModelIso f q hq hP).hom ≫ k) hn

/-- 同じ入力への可換な模型の射は、標準の導来源からの比較を変えない。 -/
theorem nativeCompletedComparison_model_change (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P Q : Complex R}
    (q : P ⟶ total K) (hq : QuasiIso q) (hP : complexKFlat R P)
    (q' : Q ⟶ total K) (hq' : QuasiIso q') (hQ : complexKFlat R Q)
    (h : P ⟶ Q) (comm : q = h ≫ q') :
    (nativeCompletedScalarModelIso f x q hq hP).hom ≫ finiteCompletedBaseChangeModelComparison f x K q =
      (nativeCompletedScalarModelIso f x q' hq' hQ).hom ≫ finiteCompletedBaseChangeModelComparison f x K q' := by
  have hs : (nativeCompletedScalarModelIso f x q' hq' hQ).hom =
      (nativeCompletedScalarModelIso f x q hq hP).hom ≫
        DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) := by
    have hn := nativeCompletedScalarModelIso_naturality f x q hq hP q' hq' hQ
      (𝟙 (total K)) h (by simpa only [Category.comp_id] using comm)
    rw [DerivedCategory.Q.map_id (total K),
      (complexDerivedExtension f).map_id (DerivedCategory.Q.obj (total K)),
      (finiteDerivedCompletionFunctor (fun j => f (x j))).map_id
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K))), Category.id_comp] at hn
    exact hn
  have hc : DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) ≫
        finiteCompletedBaseChangeModelComparison f x K q' =
      finiteCompletedBaseChangeModelComparison f x K q := by
    have hn := finiteCompletedBaseChangeModelComparison_naturality f x (𝟙 K) q q' h
      (by rw [(cochainProductTotalizationFunctor (ModuleCat.{u} R)).map_id K, Category.comp_id]; exact comm)
    rw [(standardCompletedRowsFunctor f x).map_id K,
      (cochainProductTotalizationFunctor (ModuleCat.{u} S)).map_id ((standardCompletedRowsFunctor f x).obj K),
      DerivedCategory.Q.map_id
        ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).obj ((standardCompletedRowsFunctor f x).obj K))] at hn
    exact hn.trans (Category.comp_id (finiteCompletedBaseChangeModelComparison f x K q))
  calc
    _ = (nativeCompletedScalarModelIso f x q hq hP).hom ≫
        (DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) ≫
            finiteCompletedBaseChangeModelComparison f x K q') := by rw [hc]
    _ = _ := by rw [← Category.assoc, ← hs]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
