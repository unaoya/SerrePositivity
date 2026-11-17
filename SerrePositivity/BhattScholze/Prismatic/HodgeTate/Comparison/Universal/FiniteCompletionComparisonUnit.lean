module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteDerivedReflection

/-!
# 元の有限完備化の模型比較と元の単位

## 概要
指定した元の模型同型で移した完備化比較は、元の有限完備化単位を保つ。

## 方針
元の比較の単位の式と、標準単位の自然性を使う。

## 規約
導来対象の模型の選択や有限完備化比較を変えない。

## 使われ方
p・pの元の模型比較の単位を、座標の型の移送なしで検査する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の模型同型と同じ有限完備化比較の単位。 -/
theorem finiteCompletionComparisonIso_unit {s : ℕ} (x : Fin s → R)
    {X : DerivedCategory (ModuleCat.{u} R)} {K : Complex R} (n : X ≅ DerivedCategory.Q.obj K) :
    DerivedCategory.Q.map (finiteCompletionUnit x K) ≫
      ((finiteDerivedCompletionFunctor x).mapIso n ≪≫
        (finiteDerivedCompletionComparison x).app K).inv =
    n.inv ≫ (finiteDerivedCompletionUnit x).app X := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
  rw [← finiteDerivedCompletionUnit_comparison]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simpa only [Functor.id_map] using ((finiteDerivedCompletionUnit x).naturality n.inv).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
