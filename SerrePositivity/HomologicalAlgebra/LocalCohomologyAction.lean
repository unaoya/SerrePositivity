module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# 局所コホモロジー上の具体的な乗法射

任意の `R` 代数 `C` の元による乗法は `R` 線形であり、
`localCohomology J i` の関手性から実際の局所コホモロジーの自己射を与える。
`C` の有限生成性は要求しない。

Mathlib の局所コホモロジー関手には現在、加法性・線形性のインスタンスがない。
ここでは自己射を直接定義し、未証明の `C` 加群構造は導入しない。
したがって外部の消滅定理は、これらの具体的な自己射が零という形で述べられる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory

variable {R : Type u} [CommRing R] (J : Ideal R) (i : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]

/-- 有限性を仮定しない代数 `C` の、`J` を台とする実際の局所コホモロジー。 -/
abbrev localCohomologyModule : ModuleCat.{u} R :=
  (localCohomology J i).obj (ModuleCat.of R C)

/-- `C` の元の乗法が局所コホモロジーに誘導する具体的な自己射。 -/
def localCohomologyScalarEndomorphism (c : C) :
    localCohomologyModule J i C ⟶ localCohomologyModule J i C :=
  (localCohomology J i).map (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- 単位元の乗法から誘導される射は恒等射。 -/
@[simp] theorem localCohomologyScalarEndomorphism_one :
    localCohomologyScalarEndomorphism J i C 1 = 𝟙 _ := by
  unfold localCohomologyScalarEndomorphism
  have h : ModuleCat.ofHom (LinearMap.mulLeft R (1 : C)) = 𝟙 (ModuleCat.of R C) := by
    ext c
    simp
  rw [h]
  exact (localCohomology J i).map_id _

/-- 乗法の合成は局所コホモロジーの自己射の合成に移る。 -/
theorem localCohomologyScalarEndomorphism_mul (a b : C) :
    localCohomologyScalarEndomorphism J i C (a * b) =
      localCohomologyScalarEndomorphism J i C b ≫
        localCohomologyScalarEndomorphism J i C a := by
  unfold localCohomologyScalarEndomorphism
  rw [← Functor.map_comp]
  congr 1
  ext c
  simp

end SerrePositivity.HomologicalAlgebra
