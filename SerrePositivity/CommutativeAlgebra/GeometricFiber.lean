module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# 幾何ファイバーでの推移性

## 概要

論文の Theorem 3.1 と Lemma 3.5c の仮定「有限群 `G` が `Spec T → Spec A` のすべての幾何ファイバーの
点に推移的に作用する」を定義する。幾何ファイバーとは、`Spec A` の点を代数閉体 `Ω` で表した
（`A → Ω`）ときのファイバー `Spec(T ⊗_A Ω)` のことである。そこでここでは、代数閉な `A` 体 `Ω` ごとに
`G` の `Spec(T ⊗_A Ω)` への作用が推移的であること、と定式化する。

## 内容

- `tensorAction A T G Ω g`：`g ∈ G` が `T` に作用するとき、`T ⊗_A Ω` の `A` 代数自己準同型
  `t ⊗ ω ↦ (g • t) ⊗ ω`。`G` の作用が `A` 線形（`SMulCommClass G A T`）なので定まる。
- `IsGeometricallyTransitive A T G`：すべての代数閉な `A` 体 `Ω` と `Spec(T ⊗_A Ω)` の二点 `x`、`y` に
  ついて、`g ∈ G` があって、`g` の誘導する `Spec` の写像が `x` を `y` に送る。

Theorem 3.1 の入力（`Inputs/Descent.lean`）、Lemma 3.5c（`Paper/Lemma3_5.lean`）、§5 の設定
（`Paper/Section5/`）で仮定として使う。この条件自体の性質はここでは示さない。
-/

@[expose] public section

universe u

open TensorProduct

namespace SerrePositivity

variable (A T G : Type u) [CommRing A] [CommRing T] [Algebra A T] [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- `g ∈ G` が誘導する `T ⊗_A Ω` の `A` 代数自己準同型 `t ⊗ ω ↦ (g • t) ⊗ ω`。`g` の `T` への作用は
`A` 代数準同型（`MulSemiringAction.toAlgHom`）なので、`Ω` 側を恒等写像としてテンソル積に拡張する。 -/
noncomputable def tensorAction (Ω : Type u) [CommRing Ω] [Algebra A Ω] (g : G) :
    T ⊗[A] Ω →ₐ[A] T ⊗[A] Ω :=
  Algebra.TensorProduct.map (MulSemiringAction.toAlgHom A T g) (AlgHom.id A Ω)

/-- `G` が `Spec T → Spec A` のすべての幾何ファイバーの点に推移的に作用すること：すべての代数閉な
`A` 体 `Ω` について、`Spec(T ⊗_A Ω)` の任意の二点 `x`、`y` に対して、`tensorAction g` の誘導する
`Spec` の写像（`PrimeSpectrum.comap`）で `x` が `y` に移るような `g ∈ G` がある。 -/
def IsGeometricallyTransitive : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    ∀ x y : PrimeSpectrum (T ⊗[A] Ω),
      ∃ g : G, PrimeSpectrum.comap (tensorAction A T G Ω g).toRingHom x = y

end SerrePositivity
