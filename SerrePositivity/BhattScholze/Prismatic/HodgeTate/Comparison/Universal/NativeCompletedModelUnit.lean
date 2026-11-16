module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NativeCompletedModelAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteDerivedReflection
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 元の完備模型の同型と元の単位

## 概要
元の半自由模型から完備模型への単位を標準の導来底変換の単位へ戻す。

## 方針
元の有限完備化単位の自然性と、元の複体模型の比較を使う。

## 規約
指定模型の同型を再選択しない。

## 使われ方
κの始域の指定同型が元の完備化単位を保つことを確認する。
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

/-- 元の完備模型同型は、同じ模型の元の完備化単位を保つ。 -/
theorem nativeCompletedScalarModelIso_unit (φ : R →+* B) {s : ℕ} (x : Fin s → R)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    DerivedCategory.Q.map (finiteCompletionUnit (fun j => φ (x j)) (baseChange φ P)) ≫
      (nativeCompletedScalarModelIso φ x q hq hP).inv =
    (nativeDerivedScalarModelIso φ q hq hP).inv ≫
      (finiteDerivedCompletionUnit (fun j => φ (x j))).app
        ((complexDerivedExtension φ).obj (DerivedCategory.Q.obj K)) := by
  let n := nativeDerivedScalarModelIso φ q hq hP
  let F := finiteDerivedCompletionFunctor (fun j => φ (x j))
  let U := finiteDerivedCompletionUnit (fun j => φ (x j))
  have hn := U.naturality n.hom
  simp only [Functor.id_map] at hn
  apply (cancel_mono (nativeCompletedScalarModelIso φ x q hq hP).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [nativeCompletedScalarModelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  change _ = n.inv ≫ U.app _ ≫ F.map n.hom ≫
    (finiteDerivedCompletionComparison (fun j => φ (x j))).hom.app (baseChange φ P)
  erw [← Category.assoc (U.app _), ← hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (finiteDerivedCompletionUnit_comparison (fun j => φ (x j)) (baseChange φ P)).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
