# 外部引用5：交点重複度の消滅定理をサイクルで証明する計画（Chow 群の基盤）

作成：2026-10-14。改訂：2026-10-14（基盤の設計と段階を具体化、原典の精読を反映）。状態：計画。実装は未着手。
引用5を外す主経路は [Adams 作用素の計画](archive/intersection-vanishing-adams.md) に移した。
この文書は、Chow 群の基盤（BlochConjecture と共有）と Roberts の経路を並行して進めるための計画である。
対象の宣言は [Inputs/IntersectionTheory.lean](../SerrePositivity/Inputs/IntersectionTheory.lean) の
`Inputs.intersectionVanishing`（Roberts–Gillet–Soulé の消滅定理、論文 (5.1)）。

## 0. 決めたこと（2026-10-14、利用者と相談）

- **経路**：Roberts の局所 Chern 指標と局所 Riemann–Roch（Fulton 第17〜18章・第20章）。
  原典の精読のあと、引用5は Adams 作用素の経路で先に外し、こちらは並行して進めると決め直した（同日）。
- **基盤の形**：スキームの上で作る。Mathlib の `AlgebraicGeometry.AlgebraicCycle`（点の上の局所有限な関数）と
  `Scheme.OrderOfVanishing`（余次元1の位数）の上に、次元で次数づけた Chow 群を作る。
- **置き場所**：このリポジトリの、論文の型に依存しない独立したディレクトリで作り、安定したら共有ライブラリへ切り出す。
  切り出し先の利用者として BlochConjecture（同じ `LEAN_Projects.nosync` 内、`notes/PLAN.md`） を想定する。

## 1. 主張と、今の引用の使われ方

正則局所環 `R` と有限生成加群 `M, N` について、`M ⊗_R N` が有限長で
`dim M + dim N < dim R` なら `χ^R(M, N) = 0`。混標数（分岐を含む）を含む。

利用先は二つ。主定理の帰着（Lemma 5.1、`IntersectionMultiplicity/Devissage`）と、
第一比較のランクの因子（Lemma 5.2、`IntersectionMultiplicity/FiniteExtension`）。
剰余標数零の正値性（[対角線論法](archive/serre-equal-characteristic.md)）もデヴィサージュでこれを使う。

## 2. 証明の骨格（Roberts）

`X = Spec R`、`d = dim R`。`F_•`、`G_•` を `M`、`N` の有限自由分解とする。
`F_•` は `Supp M` の外で完全なので、局所 Chern 指標
\[
\mathrm{ch}(F_\bullet) = \sum_i \mathrm{ch}_i(F_\bullet),\qquad
\mathrm{ch}_i(F_\bullet)\cap -\colon A_k(Y)_{\mathbb Q}\to A_{k-i}(Y\times_X \operatorname{Supp}M)_{\mathbb Q}
\]
が `X` 上の任意の `Y` に作用する（Fulton の両変数クラス `A^*(Supp M → X)`）。

1. **局所 Riemann–Roch**：`χ(F ⊗ G) = deg(ch(F) ch(G) ∩ τ(O_X))`。`τ` は Riemann–Roch 写像。
2. **正則なら Todd 類は自明**：`τ(O_X) = [X]`。
3. **次元の勘定**：`ch_j(G) ∩ [X] ∈ A_{d−j}(Supp N)` は `d − j ≤ dim N` でなければ零。
   続く `ch_i(F) ∩` は `A_{d−i−j}(Supp M ∩ Supp N)` に入り、閉点の `A_0` に落ちる項は `i + j = d`。
   可換性で順序を入れ替えると `d − i ≤ dim M` も要り、`dim M + dim N ≥ d` でなければ全ての項が零。

3 は短い。重いのは局所 Chern 指標の構成（graph construction）と 1・2。

原典の精読（2026-10-14）で分かったこと：

- **基底の取り方**：Fulton §20.1 で基底を `S = Spec R` 自身に取れる（`S` は正則、`Spec R` は `S` 上滑らか）。
  このとき `τ(O_S) = td(T_{S/S}) ∩ [S] = [S]` は定義から出て、分岐した混標数でも Cohen 構造・完備化は要らない。
  Fulton Ex. 20.1.4：`R` が正則なら `A_*(Spec R)_ℚ = ℚ·[Spec R]`。
- **両変数理論は判定法で足りる**：Fulton 定理 17.1。サイクルの水準の作用素が固有押し出し・平坦引き戻しと可換で、
  主因子（`{0} ↪ 𝔸¹`）との交叉と可換なら有理同値を通過する。一般の両変数群の公理（Prop 17.3.1、Cor 17.4 など）は不要。
- **次数ごとの可換性が Fulton にない**：`ch_i(F)·ch_j(G) = ch_j(G)·ch_i(F)` は明示されていない。
  乗法性 Ex. 18.1.5 からは全体の可換性しか出ない。局所 Chern 指標は押し出し・引き戻し・特殊化・Chern 類の合成で
  作られ、両変数類はそのすべてと可換（定理 17.1 の性質と Prop 17.3.2）なので、そこから導く。新しく証明する部分。
- **局所 Riemann–Roch**：Fulton Ex. 18.3.12。準射影の範囲なら Chow envelope と Quillen の `K_1`（Prop 18.3.2）は避けられる。
  閉点に台をもつ場合は `K_0^{m}(R) ≅ ℤ`（Koszul 複体が生成）を使えば、Koszul 複体の計算に帰着できる。
- **消滅定理は Fulton にない**（初版 1984 年）。Ex. 18.3.14 が有限長の場合の原型。最後の次数の勘定はこちらで組む。

## 3. 段階

共有層（C0〜C4）は BlochConjecture と同じ定義を使えるように作る。固有層（C5〜C8）はこのプロジェクト固有。

| 段 | 内容 | 原典 | 層 |
| --- | --- | --- | --- |
| C0 | 次元関数とサイクル：正則な基底上の有限型スキームでの次元 `δ`（Fulton §20.1）、`k` 次元サイクル `Z_k(X)`、連接層のサイクル `[𝓕]_k` | Fulton 1.1・1.5、20.1 | 共有 |
| C1 | 有理同値と Chow 群 `A_k(X)`、固有押し出し、平坦引き戻し、閉点の `A_0` の次数、除外列 | Fulton 第1章 | 共有 |
| C2 | Cartier 因子と直線束の `c_1(L) ∩`、因子との交叉（Gysin） | Fulton 第2章 | 共有 |
| C3 | 射影束 `P(E)`、Segre 類、ベクトル束の Chern 類と分裂原理、`ℚ` 係数の Chern 指標 | Fulton 第3章 | 共有 |
| C4 | Grassmann 束と普遍部分束、法錐への変形（特殊化写像） | Fulton 第5章、§14.2 | 共有の候補 |
| C5 | 両変数（作用素）クラス `A^*(Z → X)`：押し出し・引き戻し・積との可換性を備えた作用 | Fulton 第17章 | 固有（Bloch の作用素型クラスと設計を合わせる） |
| C6 | 局所 Chern 指標：graph construction による構成と、台・加法性・乗法性・可換性・次数のずれ | Fulton §18.1、Roberts の本 第11〜12章 | 固有 |
| C7 | 局所 Riemann–Roch と、正則なら `τ(O_X) = [X]` | Fulton 第18章・§20.1、Roberts の本 第12〜13章 | 固有。最も深い |
| C8 | 次元の勘定と `χ` との接続から `intersectionVanishing` を証明 | Roberts 1985 | 固有 |

## 4. 設計の要点（未決のものは §6）

- **次元の次数づけ**：Bloch は ℂ 上の準射影スキーム、こちらは正則局所環の Spec とその上の射影スキーム。
  両方を覆うため、正則（または普遍鎖状）な Noether 基底上の有限型スキームで Fulton §20.1 の次元関数を使う。
  ℂ 上なら通常の次元と一致する。
- **係数**：サイクルは `ℤ` 係数で定義し、Chern 指標以降は `ℚ` 係数。
- **未証明の扱い**：このリポジトリの方針どおり、深い結果は出典を docstring に書いた名前つきの定理（`sorry`）として置く。
  `axiom` と仮定のクラスは使わない（Bloch の方針 D1 とも一致）。
- **既存の資産**：台つき perfect 複体の `K_0`（`PerfectComplex/K0`）を局所 Chern 指標の定義域に使う。
  Koszul 複体・有限自由分解・Tor の長さの API はこのリポジトリのものを使う。
- **ディレクトリ**：`SerrePositivity/IntersectionTheory/`（仮称）。論文の型（`Paper/`）を import しない。
  共有層（C0〜C4）は名前空間も分け、切り出しやすくする。

## 5. 進め方

1. C0〜C1 を作る。Mathlib の `AlgebraicCycle` の次元つけと押し出しの重みを、次元関数 `δ` に合わせて使う。
2. C6・C7 を名前つきの引用として先に置き（局所 Chern 指標の存在と性質、局所 Riemann–Roch）、C8 を完成させる。
   この時点で `intersectionVanishing` の直接の `sorry` は消え、未証明は Chern 指標と Riemann–Roch の引用に移る。
   件数は増えるが、各引用の範囲は原典の定理に一致する。
3. C2〜C5 を作り、C6 の構成を証明に置き換える。
4. C7 を証明する。
5. 共有層が安定したら共有ライブラリへ切り出し、BlochConjecture から使う。

## 6. 相談して決めること

- **両変数クラスの範囲**：定理 17.1 型の判定法と作用素の合成に絞る見込み（精読の結果）。
- **graph construction の代わり**：完結した代数的な代替は見つからなかった（精読の結果）。graph construction で作る。
- **切り出しの時期と依存の向き**：BlochConjecture の Foundations とどの段で定義を揃えるか。
- **Adams の経路との関係**：引用5を Adams の経路で外したあと、こちらの経路の到達点
  （局所 Chern 指標、局所 Riemann–Roch）を何に使うか（Bloch の基盤、別の定理）。

## 7. 参照

- W. Fulton, *Intersection Theory*（第1〜3章、第5章、第14章、第17〜18章、第20章）。
- P. Roberts, *Multiplicities and Chern Classes in Local Algebra*（第11〜13章）。
- P. Roberts, *The vanishing of intersection multiplicities of perfect complexes*, Bull. AMS 13 (1985)。
- H. Gillet, C. Soulé, *Intersection theory using Adams operations*, Invent. Math. 90 (1987)（採らない経路）。
- Mathlib：`AlgebraicGeometry/AlgebraicCycle/Basic.lean`、`AlgebraicGeometry/OrderOfVanishing.lean`、
  `RingTheory/OrderOfVanishing/`。
- BlochConjecture：`notes/PLAN.md`（D2 Chow 群、D8 K 理論の範囲）、`notes/mathlib-survey-2026-10-10.md`。
