module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeDerivedScalarModels
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule

/-!
# 元の上に有界な射影模型のK-flat性

## 概要
元の上に有界な導来模型は、元の各項の射影性からK-flatである。

## 方針
元の各項の射影性をflat性へ移し、元の上に有界なflat複体の法則を使う。

## 規約
元の模型の複体と同型を変えず、有限射影次元を仮定しない。

## 使われ方
元の剰余行で、非有界の標準底変換と上に有界な指定底変換を照合する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 元の上に有界な射影模型は、同じ元の複体のK-flat模型である。 -/
theorem boundedAboveDerivedModel_kFlat {X : DerivedCategory (ModuleCat.{u} R)}
    (P : BoundedAboveDerivedModel X) : complexKFlat R P.complex := by
  apply complexKFlat_of_flat_boundedAbove R P.complex P.bound
  · intro i hi
    exact P.complex.isZero_of_isStrictlyLE P.bound i hi
  · intro i
    haveI := P.projective i
    infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
