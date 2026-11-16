module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeDerivedScalarModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeDerivedScalarModels
import all SerrePositivity.DifferentialGraded.Derived.ScalarExtension

/-!
# 元の非有界K-flat模型と標準底変換の増大

## 概要
元の指定模型で標準導来底変換を計算し、その模型の同じ元の増大を保つ。

## 方針
元の標準増大の自然性と、元の分解の擬同型性を使う。

## 規約
任意の同型を選び直さず、元のnativeDerivedScalarModelIsoを使う。

## 使われ方
元の剰余行の上に有界な指定比較との単位の一致を固定する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の指定K-flat模型の同型と元の増大の合成は、元の標準増大そのもの。 -/
@[reassoc] theorem nativeDerivedScalarModelIso_comp_augmentation (f : R →+* S)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (nativeDerivedScalarModelIso f q hq hP).hom ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) =
      (complexDerivedExtensionAugmentation f).app K := by
  haveI := hq
  apply (cancel_epi ((complexDerivedExtension f).map (DerivedCategory.Q.map q))).mp
  rw [← Category.assoc, derived_map_comp_nativeDerivedScalarModelIso]
  exact ((complexDerivedExtensionAugmentation f).naturality q).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
