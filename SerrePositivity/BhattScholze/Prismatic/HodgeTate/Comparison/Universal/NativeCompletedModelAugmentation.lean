module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NativeScalarModelAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 元の完備した模型同型と同じ増大

## 概要
指定された完備K-flat模型の同型は、その模型の元の増大を標準の完備増大へ送る。

## 方針
元の完備化比較の自然性と、非有界な標準底変換の増大の正規化を使う。

## 規約
模型を射から逆算せず、元のnativeCompletedScalarModelIsoを保つ。

## 使われ方
元のκの項ごとの写像と元の上に有界な指定同型を照合する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B]

/-- 元の完備模型の同型と元の増大は、元の標準完備増大に一致する。 -/
@[reassoc] theorem nativeCompletedScalarModelIso_comp_augmentation
    (φ : R →+* B) {s : ℕ} (x : Fin s → R)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (nativeCompletedScalarModelIso φ x q hq hP).hom ≫
      DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => φ (x j))).map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q)) =
    (finiteDerivedCompletionFunctor (fun j => φ (x j))).map
        ((complexDerivedExtensionAugmentation φ).app K) ≫
      (finiteDerivedCompletionComparison (fun j => φ (x j))).hom.app (baseChange φ K) := by
  let F := finiteDerivedCompletionFunctor (fun j => φ (x j))
  have hn := (finiteDerivedCompletionComparison (fun j => φ (x j))).hom.naturality
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q)
  change F.map (DerivedCategory.Q.map
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q)) ≫
      (finiteDerivedCompletionComparison (fun j => φ (x j))).hom.app (baseChange φ K) =
    (finiteDerivedCompletionComparison (fun j => φ (x j))).hom.app (baseChange φ P) ≫
      DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => φ (x j))).map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q)) at hn
  simp only [nativeCompletedScalarModelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
    nativeDerivedScalarModelIso_comp_augmentation]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
