module

public import SerrePositivity.HomologicalAlgebra.PerfectRingTor

/-!
# 完全標数 p 環の Tor 独立性

## 概要
完全標数 p 環の任意の図式に対し、正次数の通常の Tor が零となる。
BS 著者版 Lemma 10.3（印刷 pp.78–79）の証明中の mod p 入力を供給する。

## 方針
既存の自由完全多項式代数による平坦な全射表示と Tor 底変換の証明を再利用する。
原典が参照する BS17 Lemma 3.16 を引用しない。原典の証明は Tor を単体的可換代数
`B_•(A,A,B) ⊗_A C` のホモトピー群として表し、Frobenius が同型かつ正次数で零を誘導することを使う
（p 乗写像は加法的でないので、基点付き単体集合のホモトピー群を経由する必要がある）。
ここではその単体的議論を使わず、平坦な全射表示による代数的な証明をとる。

## 規約
三環は同じ universe に置き、Mathlib の第 2 変数で導来する `Tor` を使う。

## 使われ方
BS Lemma 10.3 の完全環に関する明示仮定を、追加の数学的仮定なしに満たすための入口である。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

/--
## 概要
完全標数 p 環 A と完全 A 代数 B,C に対し、すべての正次数で Tor_i^A(B,C) は零である。
出典上の利用箇所は BS 著者版 Lemma 10.3（印刷 pp.78–79）の証明である。

## 方針
自由完全多項式代数の平坦な全射表示と Tor-acyclic 底変換による既存の
`perfectRing_tor_subsingleton` を適用し、台加群の自明性を圏論的な零対象性へ移す。

## 規約
p は素数とし、三環の標数と完全性を明示する。全射性・平坦性・有限性は仮定しない。

## 使われ方
BS Lemma 10.3 の証明が必要とする完全環の Tor 独立性の入力を供給する。
-/
theorem tor_vanishing_of_perfect
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]
    [PerfectRing A p] [PerfectRing B p] [PerfectRing C p] :
    ∀ i : ℕ, 0 < i →
      IsZero (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A B)).obj (ModuleCat.of A C)) := by
  intro i hi
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (perfectRing_tor_subsingleton (p := p) B C i hi)

end SerrePositivity
