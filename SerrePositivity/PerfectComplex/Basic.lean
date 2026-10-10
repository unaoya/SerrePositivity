module

public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# 閉点に台をもつ完全複体と、その二つの Euler 評価

## 概要

このファイルは、論文の §3（Lemma 3.5 とその周辺）で主役になる対象を定義する。
環 `T` 上の有界な複体 `P` で、各項が有限生成自由加群であり、しかも「閉点の近くにしか台をもたない」
ものを考え、そのホモロジーの長さの交代和として二種類の Euler 標数を定める。定義だけを置き、
性質（台の条件が基底変更やひねりで保たれること、Euler 標数が `K₀` 上の準同型になること）は
別のファイルで示す。

## 背景

論文の Lemma 3.5 は、次の状況で二つの Euler 標数を比べる主張である。`A` を局所環、`T` を `A` 上
有限な環、`z = (z_1, …, z_e)` を `A` の極大イデアルを（根基の意味で）生成する列とし、`T` 上の
完全複体 `P` で、台が `z` の零点集合、すなわち `T` の閉点に含まれるものをとる。このとき

- 通常の Euler 標数 `χ_T(P) = Σ_i (-1)^i ℓ_T(H_i(P))`（`ℓ_T` は `T` 加群としての長さ）と、
- 正規化長さ `λ` による Euler 標数 `χ_C(P) = Σ_i (-1)^i λ(H_i(P ⊗_T C))`（`C` は `T` 代数で、
  `λ` は `C` 加群の「正規化された長さ」。`NormalizedLength.lean`）

が定まり、Lemma 3.5 は、有限群 `G` の作用でひねった複体 `g^*P` にわたる和について
`Σ_g χ_T(g^*P) = Σ_g χ_C(g^*P)` を主張する。本ファイルの定義はこの主張を書くための語彙である。

## 定義

- `IsSupported z P`：`P` が `z` の零点集合に台をもつことの判定条件。ある冪 `v` があって、
  すべての `j` について `z_j^v • 𝟙 P` が零ホモトピックであること、で定義する。
  論文 §3.1 では台を局所化で述べるが、ここでは零ホモトピーで定義する。理由は、
  この形なら基底変更（`P ↦ P ⊗_T C`）やひねり（`P ↦ g^*P`）で保たれることが関手性から直ちに出るため
  （`Support.lean`）。ホモロジーの台による条件との同値は、有界な有限射影複体について
  `Support.lean` の `isSupported_iff_homologySupport` で示す。
- `IsPerfectSupported z P`：`P` が有界で、各項が有限生成自由加群で、`z` に台をもつこと。
  論文の「`V(zT)` に台をもつ完全複体」の具体的なモデルである。各項を射影的ではなく自由に
  限定しているのは、局所環上では有限生成射影加群は自由であり、また自由性は基底変更で保たれて
  扱いやすいためである。一般の完全複体（導来圏の完全対象）との同値は示していない。
- `PerfSupp T z`：`IsPerfectSupported z P` をみたす複体 `P` の全体（部分型）。
  `K₀` の生成元の集合として使う（`K0.lean`）。
- `chiOrd P`：通常の Euler 評価 `χ_T(P)`。
- `chiLam lam φ P`：正規化長さ `lam` による Euler 評価 `χ_C(P)`。`φ : T →+* C` が `C` の
  `T` 代数構造を与える。
- `twist g P`：ひねり `g^*P`。群 `G` の元 `g` が定める環準同型 `T → T` に沿った係数制限。

## 規約と注意

- 添字は cochain（`ComplexShape.up ℤ`）で、論文の homological な `i` 次ホモロジー `H_i` は
  ここでは `-i` 次 `H^{-i}` である。符号については `(-1)^{-i} = (-1)^i` なので、cochain の次数 `n`
  について `(-1)^n ℓ(H^n)` を足せば論文の交代和と一致する。符号 `(-1)^n` は `Int.negOnePow n` で書く。
- 二つの Euler 評価は実数値で、無限に関する「ゴミの値」の規約を含む：長さが無限の項は
  `ENat.toNat`・`ENNReal.toReal` によって `0` と数え、非零の項が無限個あるときは `finsum` の値は
  `0` である。したがって定義そのものはどんな複体にも意味をもつが、加法性などの性質は、
  `P` が有界でホモロジーが有限長のときにだけ成り立つ（`OrdinaryEuler.lean`、`NormalizedEuler.lean`）。
- `twist` は反変的である：`twist a (twist b P) ≅ twist (b * a) P`。このため `K₀` への `G` の
  左作用は `g • [P] := [twist g⁻¹ P]` で定める（`K0.lean`）。

## 使われ方

`Support.lean`（台の条件の閉包性）、`Closure.lean`（`IsPerfectSupported` の閉包性）、
`K0.lean`（台つき完全複体の `K₀` と基底変更・ひねりの作用）、`OrdinaryEuler.lean`・
`NormalizedEuler.lean`（二つの Euler 評価の加法性と `K₀` への降下）、
`Paper/Lemma3_5.lean`（Lemma 3.5 の主張と証明）、`Paper/Section5/`（§5 での利用）。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- 複体 `P` が列 `z = (z_1, …, z_e)` の零点集合に台をもつことの判定条件。
ある自然数 `v` があって、すべての `j` について `z_j^v` 倍の射 `z_j^v • 𝟙 P : P ⟶ P` が
零ホモトピックであること。

直観的には、`z_j` の冪で消えるのだから `P` は `z_j` を可逆にすると消える、つまり
`P` は `z_j ≠ 0` となる点には台をもたない、ということである。局所化 `P[1/z_j] ≃ 0` ではなく
零ホモトピーで定義するのは、複体の関手（基底変更・係数制限）がホモトピーを保つので
台の条件が自動的に移るからである。冪 `v` は `j` によらず共通にとっているが、各 `j` ごとに
冪があれば共通の冪がとれる（`Support.lean` の `isSupported_of_forall`）。 -/
def IsSupported {e : ℕ} (z : Fin e → T) (P : CochainComplex (ModuleCat.{u} T) ℤ) : Prop :=
  ∃ v : ℕ, ∀ j : Fin e, Nonempty (Homotopy ((z j) ^ v • 𝟙 P) 0)

/-- `P` が `z` の零点集合に台をもつ完全複体であること。すなわち、`P` は有界で、各項が
有限生成自由 `T` 加群で、`z` に台をもつ（`IsSupported z P`）。

論文の「`V(zT)` に台をもつ完全複体」をこの具体的な形で表す。`K₀` の生成元（`PerfSupp`）の
条件であり、Lemma 3.5 の対象は `z` を `A` の正則パラメータ系の `T` での像にとったものである。
証明の中では、写像錐・シフト・基底変更・ひねりでこの条件が保たれること（`Closure.lean`）を
繰り返し使う。 -/
structure IsPerfectSupported {e : ℕ} (z : Fin e → T) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    Prop where
  /-- 有界性：ある `a ≤ b` があって、`a` 次より下と `b` 次より上の項は零。
  Euler 評価が有限和になるために要る。 -/
  bounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → Limits.IsZero (P.X i)
  /-- 各項は自由 `T` 加群。射影性（K 射影的な複体として持ち上げに使う）と、基底変更後も
  自由であることの両方に使う。 -/
  free : ∀ i, Module.Free T (P.X i)
  /-- 各項は有限生成。ホモロジーが有限生成、したがって（台の条件とあわせて）有限長に
  なるために要る。 -/
  finite : ∀ i, Module.Finite T (P.X i)
  /-- `z` の零点集合に台をもつ（`IsSupported z P`）。 -/
  supported : IsSupported z P

variable (T) in
/-- `z` に台をもつ完全 `T` 複体の全体。`IsPerfectSupported z P` をみたす複体 `P` の部分型で、
`P.1` が複体、`P.2` がその証明である。`K₀`（`K0.lean`）は、この型の上の自由アーベル群を
ホモトピー同値と写像錐の関係式で割って作る。 -/
abbrev PerfSupp {e : ℕ} (z : Fin e → T) : Type (u + 1) :=
  {P : CochainComplex (ModuleCat.{u} T) ℤ // IsPerfectSupported z P}

/-- 通常の Euler 評価 `χ_T(P) = Σ_n (-1)^n ℓ_T(H^n(P))`。`ℓ_T` は `T` 加群としての長さ
（`Module.length`、`ℕ∞` 値）で、実数に移して交代和をとる。

長さが無限の項は `ENat.toNat` によって `0` と数え、非零の項が無限個あれば `finsum` の値は `0` に
なる。この「ゴミの値」の規約のおかげで、どんな複体 `P` に対しても定義できるが、ホモトピー不変性や
写像錐についての加法性は、`P` が有界でホモロジーが有限長のときに示す（`OrdinaryEuler.lean`）。
論文の homological な添字では `Σ_i (-1)^i ℓ(H_i(P))` だが、`H_i = H^{-i}` と `(-1)^{-i} = (-1)^i`
からこれは上の式と同じである。通常の長さは正規化長さの特別な場合（`NormalizedLength.ordinary`）
なので、`chiOrd` は `chiLam` の仲間 `lambdaEuler` の特別な場合でもある
（`NormalizedEuler.lean` の `chiOrd_eq_lambdaEuler_ordinary`）。 -/
noncomputable def chiOrd (P : CochainComplex (ModuleCat.{u} T) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * ((Module.length T (P.homology i)).toNat : ℝ)

variable {C : Type u} [CommRing C]

/-- 正規化長さ `lam` による Euler 評価 `χ_C(P) = Σ_n (-1)^n λ(H^n(P ⊗_T C))`。
まず `φ : T →+* C` に沿って `P` を `C` 上に基底変更し（`baseChange φ P`、各項に `C ⊗_T -` を施した
複体）、そのホモロジーを `C` 加群の正規化長さ `lam : NormalizedLength C J`（`ℝ≥0∞` 値）で測って
交代和をとる。

論文の `χ_C(P)`（§3.4）に当たる。無限の長さは `ENNReal.toReal` で `0` と数える。`chiOrd` と同じく
定義はどんな複体にも意味をもち、加法性と `K₀` への降下は、ホモロジーの `λ` が有限であるという
仮定のもとで示す（`NormalizedEuler.lean` の `chiLamHom_of_finite`）。その有限性が Lemma 3.5a の
正規化長さ側の内容である。 -/
noncomputable def chiLam {J : Ideal C} (lam : NormalizedLength C J) (φ : T →+* C)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len ((baseChange φ P).homology i)).toReal

variable {G : Type u} [Group G] [MulSemiringAction G T]

/-- ひねり `g^*P`：群 `G` の元 `g` が定める環準同型 `T → T`（`t ↦ g • t`）に沿って、複体 `P` の
各項の係数を制限したもの。項と微分は `P` と同じ集合・同じ写像で、`T` の作用だけが
`t • x := (g • t) • x` に変わる。

論文 §3.4 末尾の scalar twisting に当たり、Lemma 3.5c の「共役和」`Σ_g χ_T(g^*P)` に現れる。
係数制限は複体の関手なので、ホモトピー同値・写像錐・台の条件を保つ（`Support.lean`、
`Closure.lean`）。合成については `twist a (twist b P) ≅ twist (b * a) P` と順序が逆になるので、
`K₀` への `G` の左作用は `g • [P] := [twist g⁻¹ P]` で定める（`K0.lean`）。 -/
noncomputable abbrev twist (g : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    CochainComplex (ModuleCat.{u} T) ℤ :=
  ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomologicalComplex _).obj P

end SerrePositivity
