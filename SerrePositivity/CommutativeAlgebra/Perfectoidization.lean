module

public import SerrePositivity.Inputs.Perfectoidization
public import Mathlib.RingTheory.FinitePresentation
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdeal

/-! # 普遍性で選んだ perfectoid 化

有限代数の perfectoid 化の存在を引用し、その普遍対象を選ぶ。
構成に長さやホモロジーの性質を組み込まず、引用定理が規定する普遍性を保持する。
-/

@[expose] public section

universe u

namespace SerrePositivity

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 有限代数 `S` の perfectoid 化。存在定理で保証される普遍対象を選ぶ。 -/
noncomputable def Perfectoidization : Type u :=
  (Inputs.exists_perfectoidization_of_finite R S p hR).choose

/-- 存在定理で選んだ普遍対象の環構造。 -/
noncomputable instance : CommRing (Perfectoidization R S p hR) :=
  (Inputs.exists_perfectoidization_of_finite R S p hR).choose_spec.choose

/-- 元の代数から perfectoid 化への標準写像。 -/
noncomputable def toPerfectoidization : S →+* Perfectoidization R S p hR :=
  (Inputs.exists_perfectoidization_of_finite R S p hR).choose_spec.choose_spec.choose

/-- 選んだ環と標準写像は perfectoid 化の普遍性を満たす。 -/
theorem isPerfectoidization_toPerfectoidization :
    IsPerfectoidization p (toPerfectoidization R S p hR) :=
  (Inputs.exists_perfectoidization_of_finite R S p hR).choose_spec.choose_spec.choose_spec

/-- 普遍写像による元の代数 `S` の作用。 -/
noncomputable instance : Algebra S (Perfectoidization R S p hR) :=
  (toPerfectoidization R S p hR).toAlgebra

/-- Perfectoid 化への標準写像は代数構造の写像である。 -/
theorem algebraMap_perfectoidization :
    algebraMap S (Perfectoidization R S p hR) = toPerfectoidization R S p hR := rfl

/-- `R → S` と普遍写像を合成した基底環の作用。 -/
noncomputable instance : Algebra R (Perfectoidization R S p hR) :=
  ((toPerfectoidization R S p hR).comp (algebraMap R S)).toAlgebra

/-- 基底環の作用と `S` の作用は合成の定義から両立する。 -/
instance : IsScalarTower R S (Perfectoidization R S p hR) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl


end SerrePositivity
