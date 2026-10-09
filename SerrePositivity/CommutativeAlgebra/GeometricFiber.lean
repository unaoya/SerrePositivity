module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# 幾何ファイバーでの推移性（論文 Theorem 3.1、Lemma 3.5 の仮定）

有限群 `G` が `A` 代数 `T` に作用するとき、「`Spec T → Spec A` のすべての幾何ファイバーの点に
`G` が推移的に作用する」を、代数閉な `A` 体 `Ω` ごとに `Spec (T ⊗_A Ω)` の点への作用の推移性として書く。
`G` の `T ⊗_A Ω` への作用は左因子への作用から誘導される。
-/

@[expose] public section

universe u

open TensorProduct

namespace SerrePositivity

variable (A T G : Type u) [CommRing A] [CommRing T] [Algebra A T] [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- `g ∈ G` が誘導する `T ⊗_A Ω` の `A` 代数自己準同型。 -/
noncomputable def tensorAction (Ω : Type u) [CommRing Ω] [Algebra A Ω] (g : G) :
    T ⊗[A] Ω →ₐ[A] T ⊗[A] Ω :=
  Algebra.TensorProduct.map (MulSemiringAction.toAlgHom A T g) (AlgHom.id A Ω)

/-- `G` が `Spec T → Spec A` のすべての幾何ファイバーの点に推移的に作用する。 -/
def IsGeometricallyTransitive : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    ∀ x y : PrimeSpectrum (T ⊗[A] Ω),
      ∃ g : G, PrimeSpectrum.comap (tensorAction A T G Ω g).toRingHom x = y

end SerrePositivity
