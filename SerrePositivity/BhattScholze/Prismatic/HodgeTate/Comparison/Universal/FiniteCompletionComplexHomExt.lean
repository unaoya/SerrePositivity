module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteDerivedReflection

/-!
# 元の複体の有限完備化からの射の外延性

## 概要
指定された複体の有限完備化から完備な終域への射は、元の合成単位上で決まる。

## 方針
元の複体模型の比較と有限導来完備化のHomの普遍性を使う。

## 規約
複体の模型比較も完備化の単位も元のものを使う。

## 使われ方
元のκの射と指定された被覆比較を同じ元の単位で検査する。
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

/-- 元の複体の有限完備化からの射は、元の合成単位上で判定できる。 -/
theorem finiteCompletionComplexHom_ext {s : ℕ} (x : Fin s → R) (K : Complex R)
    (Y : DerivedCategory (ModuleCat.{u} R)) (hY : ∀ j, IsComplete R (x j) Y)
    {f g : DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K) ⟶ Y}
    (h : DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ f =
      DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ g) : f = g := by
  let c := (finiteDerivedCompletionComparison x).hom.app K
  have hc := finiteDerivedCompletionUnit_comparison x K
  apply (cancel_epi c).mp
  apply finiteDerivedCompletionHom_ext x (DerivedCategory.Q.obj K) Y hY
  calc
    _ = DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ f := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ f) hc
    _ = DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ g := h
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ g) hc.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
