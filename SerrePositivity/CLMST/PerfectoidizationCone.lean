module

public import SerrePositivity.CommutativeAlgebra.Perfectoidization
public import SerrePositivity.HomologicalAlgebra.DerivedModuleCone

/-! # perfectoid 化の標準写像の実導来錐

選んだ普遍 perfectoid 環への標準写像を R 線形写像にし、零次数の加群写像の
標準 mapping cone を実導来圏へ送る。未知の述語として錐を仮定しない。
存在入力に相対的な構成であり、新しい perfectoid 化の選択は行わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 普遍 perfectoid 化への標準写像を、元の基底 R 上の線形写像として扱う。 -/
def perfectoidizationModuleMap : S →ₗ[R] Perfectoidization R S p hR :=
  (IsScalarTower.toAlgHom R S (Perfectoidization R S p hR)).toLinearMap

/-- 線形写像の値は、選んだ perfectoid 化への既存の標準写像と同じ。 -/
@[simp] theorem perfectoidizationModuleMap_apply (s : S) :
    perfectoidizationModuleMap R S p hR s = toPerfectoidization R S p hR s := rfl

/-- 標準写像 S[0]→S_perfd[0] の、実導来圏 D(R) での錐。 -/
abbrev perfectoidizationCone : DerivedCompletion.ConcreteDerivedCategory R :=
  moduleMapCone R (perfectoidizationModuleMap R S p hR)

/-- 標準写像とその錐の実際の完全三角形。 -/
abbrev perfectoidizationTriangle : Triangle (DerivedCompletion.ConcreteDerivedCategory R) :=
  moduleMapConeTriangle R (perfectoidizationModuleMap R S p hR)

/-- 標準写像と錐の三角形は、実導来圏で distinguished である。 -/
theorem perfectoidizationTriangle_distinguished :
    perfectoidizationTriangle R S p hR ∈
      distTriang (DerivedCompletion.ConcreteDerivedCategory R) :=
  moduleMapConeTriangle_distinguished R (perfectoidizationModuleMap R S p hR)

/-- 標準三角形の第三対象は、定義した実導来錐そのものである。 -/
@[simp] theorem perfectoidizationTriangle_obj₃ :
    (perfectoidizationTriangle R S p hR).obj₃ = perfectoidizationCone R S p hR := rfl

end SerrePositivity.CLMST
