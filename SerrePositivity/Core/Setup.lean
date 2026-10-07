module

public import SerrePositivity.EulerChar
public import SerrePositivity.GeometricFiber
public import SerrePositivity.Inputs.LengthAlgebra
public import SerrePositivity.NormalizedLength
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# 核の場合の設定（論文 §5.1）

`D = R/P`、`E = R/Q` に対して、§5.1 で固定されるデータをまとめる。

- `A_D ⊆ D'`：正規化基底（Lemma 2.2）と、その正則パラメータ系 `t_D`。
- `D'`：`D` の Galois 閉包での整閉包。局所整域で、有限群 `G_D` が `A_D` 上で作用する。`a_D = rank_D D'`。
- `A_E`、`E'`、`G_E`、`a_E`：同様。
- `C_D`：Theorem 2.5 の長さ代数。`D'` 代数で、正規化長さ `λ_D` をもつ。
- `ι_σ : R → D' →σ D' → C_D`：`σ ∈ G_D` でひねった `C_D` の `R` 代数構造。
- `c_σ = Σ_i (-1)^i λ_D(Tor_i^R(C_D, E'))`（論文 (5.2)）。`R` は `C_D` に `ι_σ` で作用する。

`CoreData` はデータと、型として要る instance（環、局所環、整域、代数構造、群作用）だけを持つ。
データが論文の対象であるための仮定（Lemma 2.2 の基底の性質、Galois 群であること、
幾何ファイバーでの推移性、`a_D` が階数であること、Theorem 2.5 の (2.4)–(2.6)）は
`CoreData.IsPaperData` にまとめる。塔 `Λ` は Lemma 5.4 で要るので、その段階で足す。
-/

@[expose] public section

universe u

open scoped ENNReal

namespace SerrePositivity

/-- §5.1 のデータ。`R` と素イデアル `P, Q` に対して、`D'`、`G_D`、`a_D`、`C_D`、`λ_D`、
`E'`、`G_E`、`a_E` をまとめたもの。 -/
structure CoreData (R : Type u) [CommRing R] (P Q : Ideal R) where
  /-- `D = R/P` の Galois 閉包での整閉包 `D'`。 -/
  D' : Type u
  [commRingD' : CommRing D']
  [isLocalRingD' : IsLocalRing D']
  [isDomainD' : IsDomain D']
  [algebraRD' : Algebra R D']
  [algebraDD' : Algebra (R ⧸ P) D']
  [towerD' : IsScalarTower R (R ⧸ P) D']
  /-- 正規化基底 `A_D`（Lemma 2.2）。 -/
  AD : Type u
  [commRingAD : CommRing AD]
  [isLocalRingAD : IsLocalRing AD]
  [algebraADD' : Algebra AD D']
  /-- `A_D` の次元 `h = dim D`。 -/
  hD : ℕ
  /-- `A_D` の正則パラメータ系 `t_D`。 -/
  tD : Fin hD → AD
  /-- Galois 群 `G_D = Gal(Frac D' / Frac A_D)`。`D'` に `A_D` 上の環自己同型として作用する。 -/
  GD : Type u
  [groupGD : Group GD]
  [fintypeGD : Fintype GD]
  [actionGD : MulSemiringAction GD D']
  [smulCommGD : SMulCommClass GD AD D']
  /-- `a_D = rank_D D'`。 -/
  aD : ℕ
  aD_pos : 0 < aD
  /-- `E = R/Q` の Galois 閉包での整閉包 `E'`。 -/
  E' : Type u
  [commRingE' : CommRing E']
  [isLocalRingE' : IsLocalRing E']
  [isDomainE' : IsDomain E']
  [algebraRE' : Algebra R E']
  [algebraEE' : Algebra (R ⧸ Q) E']
  [towerE' : IsScalarTower R (R ⧸ Q) E']
  /-- 正規化基底 `A_E`。 -/
  AE : Type u
  [commRingAE : CommRing AE]
  [isLocalRingAE : IsLocalRing AE]
  [algebraAEE' : Algebra AE E']
  /-- `A_E` の次元 `l = dim E`。 -/
  hE : ℕ
  /-- `A_E` の正則パラメータ系 `t_E`。 -/
  tE : Fin hE → AE
  /-- Galois 群 `G_E`。`E'` に `A_E` 上の環自己同型として作用する。 -/
  GE : Type u
  [groupGE : Group GE]
  [fintypeGE : Fintype GE]
  [actionGE : MulSemiringAction GE E']
  [smulCommGE : SMulCommClass GE AE E']
  /-- `a_E = rank_E E'`。 -/
  aE : ℕ
  aE_pos : 0 < aE
  /-- Theorem 2.5 の長さ代数 `C_D`（`D'` に対してとる。論文 §5.1「`(C_D, λ_D) = (C_{D'}, λ_{D'})`」）。 -/
  CD : Type u
  [commRingCD : CommRing CD]
  [algebraCD : Algebra D' CD]
  /-- `λ_D`：`C_D` 加群の正規化長さ。`m_{D'} C_D` の冪で消える加群の上で加法的。 -/
  lamD : NormalizedLength CD ((IsLocalRing.maximalIdeal D').map (algebraMap D' CD))

namespace CoreData

variable {R : Type u} [CommRing R] {P Q : Ideal R} (X : CoreData R P Q)

attribute [instance] commRingD' isLocalRingD' isDomainD' algebraRD' algebraDD' towerD'
  commRingAD isLocalRingAD algebraADD' groupGD fintypeGD actionGD smulCommGD
  commRingE' isLocalRingE' isDomainE' algebraRE' algebraEE' towerE'
  commRingAE isLocalRingAE algebraAEE' groupGE fintypeGE actionGE smulCommGE
  commRingCD algebraCD

/-- `ι_σ : R → D' →σ D' → C_D`。`σ ∈ G_D` でひねった `C_D` の `R` 代数構造。 -/
noncomputable def iota (σ : X.GD) : R →+* X.CD :=
  (algebraMap X.D' X.CD).comp ((MulSemiringAction.toRingHom X.GD X.D' σ).comp (algebraMap R X.D'))

/-- 論文 (5.2)：`c_σ = Σ_i (-1)^i λ_D(Tor_i^R(C_D, E'))`。`R` は `C_D` に `ι_σ` で作用する。 -/
noncomputable def c (σ : X.GD) : ℝ :=
  lambdaChi X.lamD (X.iota σ) X.E'

/-- **Lemma 5.2**（第一のノルム比較）の主張：(5.2) の各長さは有限で、
`|G_D| a_D a_E χ^R(D, E) = Σ_σ c_σ`（論文 (5.3)）。 -/
def FirstComparison : Prop :=
  (∀ (σ : X.GD) (i : ℕ), X.lamD.len (TorAlg (X.iota σ) i X.E') ≠ ⊤) ∧
    (Fintype.card X.GD : ℝ) * X.aD * X.aE * (chi R (R ⧸ P) (R ⧸ Q) : ℝ) = ∑ σ, X.c σ

/-- **(5.18) と Lemma 5.6**（第二のノルム比較と正値性）の主張：各 `σ` に対して
`b_{σ,γ}`（§4 の `C_E` による評価）があり、`|G_E| c_σ = Σ_γ b_{σ,γ}` かつ `b_{σ,γ} > 0`。

`b_{σ,γ}` は §4 の漸近的な圏での評価で、ここでは実数としてだけ扱う。
その定義と (5.18)、(5.17) の証明は M3 以降。 -/
def SecondComparison : Prop :=
  ∃ b : X.GD → X.GE → ℝ,
    (∀ σ, (Fintype.card X.GE : ℝ) * X.c σ = ∑ γ, b σ γ) ∧ ∀ σ γ, 0 < b σ γ

/-- データが論文 §5.1 の対象であるための仮定。 -/
structure IsPaperData : Prop where
  /-- `A_D ⊆ D'` は Lemma 2.2 の形の正規化基底（`D'` に対して）。 -/
  baseD : IsRegularNormalizationBase X.AD X.D' X.tD
  /-- `G_D` は `D' / A_D` の Galois 群：忠実、`A_D` 上の作用、不変環は `A_D`。 -/
  galoisD : IsGaloisGroup X.GD X.AD X.D'
  /-- `G_D` は `Spec D' → Spec A_D` の幾何ファイバーで推移的。 -/
  transitiveD : IsGeometricallyTransitive X.AD X.D' X.GD
  /-- `D'` は `D = R/P` 上有限。 -/
  finiteD : Module.Finite (R ⧸ P) X.D'
  /-- `a_D = rank_D D'`。 -/
  aD_eq : X.aD = Module.finrank (R ⧸ P) X.D'
  /-- `D'` の剰余体は `k`：`R → D' → D'/m_{D'}` は全射。 -/
  residueD : Function.Surjective ((IsLocalRing.residue X.D').comp (algebraMap R X.D'))
  /-- `(C_D, λ_D)` は Theorem 2.5 の結論 (2.4)–(2.6) をみたす（`D'` と `A_D` に対して）。 -/
  lengthD : LengthAlgebraProps X.AD X.D' X.tD X.CD X.lamD
  /-- `A_E ⊆ E'` は Lemma 2.2 の形の正規化基底。 -/
  baseE : IsRegularNormalizationBase X.AE X.E' X.tE
  /-- `G_E` は `E' / A_E` の Galois 群。 -/
  galoisE : IsGaloisGroup X.GE X.AE X.E'
  /-- `G_E` は幾何ファイバーで推移的。 -/
  transitiveE : IsGeometricallyTransitive X.AE X.E' X.GE
  /-- `E'` は `E = R/Q` 上有限。 -/
  finiteE : Module.Finite (R ⧸ Q) X.E'
  /-- `a_E = rank_E E'`。 -/
  aE_eq : X.aE = Module.finrank (R ⧸ Q) X.E'
  /-- `E'` の剰余体は `k`。 -/
  residueE : Function.Surjective ((IsLocalRing.residue X.E').comp (algebraMap R X.E'))

end CoreData

end SerrePositivity
