# K-L7：スキーム論と blowup

作成日：2026-10-18。
レーン名：K-L7（スキーム論と blowup）。
正本：`formalization-plans/k-theory-kst-route.md`。
共通の決定：`formalization-plans/foundations.md`。
本文は作業履歴ではなく、現在の設計と受入条件を記す。
実施の経緯は個々のコミットメッセージに記す。

## 1. 現在地

- L7a の Rees 次数付けとアフィン blowup の定義を実装済み。
- 零次成分の同定・基礎環上の構造射・有限生成中心での固有性を実装済み。
- 対象ビルド成功。最新の保存単位の公理監査は 754 宣言、標準三公理のみ。
- 中心の逆像の閉部分スキーム、閉埋め込み、交換式を構成済み。
- 次数一の標準アフィンチャートとその被覆性を証明済み。
- チャート上で `a · (b/a) = b` と拡大イデアル `I O = (a)` を証明済み。
- チャート上で a が非零因子であることを基礎環の仮定なしで証明済み。
- チャートの a による分母消去・係数の等式判定・a を可逆化した環と R[1/a] の同型を証明済み。
- 一般の Proj 構造射で、零次成分の素イデアルの所属と基本開集合の逆像を計算済み。
- アフィン blowup が中心の補開集合全体で同型となることを証明し、構造射と両立するスキーム同型を構成済み。
- 例外閉部分スキームのチャートへの逆像を、拡大イデアルの商の Spec と包含射まで同定済み。
- Stacks 01WQ Lemma 31.14.2 のアフィン局所モデルを有効 Cartier 条件の定義とし、アフィン例外因子について証明済み。
- 各チャートの拡大イデアルは、チャート環との実際の線形同型により階数一自由加群として自明化済み。
- 正の冪の対応チャート環の同型と係数保存、純冪チャートによる被覆性は証明済み。
- 核が零の射と分離標的による射の一意性、開基底変換での零核の保存を証明済み。
- 標準アフィン開被覆を構成し、中心外で同型な分離標的へのチャート比較の重なり上の一致と大域一意性を証明済み。
- 正の冪について基底上の実際のスキーム同型 `affineBlowupPowerIso : Bl(Iⁿ) ≅ Bl(I)` を構成済み。
- 任意の中心を保つ環準同型の Rees 次数付き写像と合成則、像中心での irrelevant ideal の包含を証明済み。
- 任意の環準同型に対する実際の blowup 比較射と、基底の Spec の射との交換式を構成済み。
- Rees 代数の係数局所化について共通分母の消去・局所化の普遍条件・実際の環同型と係数保存を証明済み。
- 斉次元の分母を同じ次数で払う補題も証明済み。
- 標準チャートの係数写像、係数保存、斉次分数の計算式、係数局所化後のチャートの共通分母消去を証明済み。
- 二つの局所化の交換とチャートの等式検出を証明し、係数局所化後のチャートの実際の環同型と係数保存を構成済み。
- 元の中心元の像に対応するチャートだけで像中心の blowup を覆うことを証明済み。
- blowup 比較射とチャートの射の交換式、標準チャートの逆像の計算を証明済み。
- 一元係数局所化の blowup 比較射の開埋め込み性と像を証明し、`affineBlowupLocalizationIso` により D(r) の逆像との実際のスキーム同型を構成済み。
- 中心を別表示のイデアルとして保持する比較射の恒等性・反変合成則・基底両立性を証明済み。
- 中心を保つ基礎環同型による blowup の実際のスキーム同型を構成済み。
- イデアル層の全アフィン開集合上の局所モデルを関手として構成し、構造射の自然性を証明済み。
- 基本開集合へのモデル比較の開埋め込み性と像の公式を証明済み。
- 共通基本開近傍での比較により、任意のアフィン開包含の局所モデル比較の単射性と開埋め込み性を証明済み。
- 任意のアフィン開包含のモデル比較の像を基礎開集合の逆像として同定済み。
- アフィン局所モデルの図式の局所的有向性を証明し、一般スキーム上の通常の `blowup` と `blowupπ` を構成済み。
- 各アフィン開集合上の実際の Rees Proj との同型と構造射の交換式を構成済み。
- 一般の blowup の分離性、アフィン局所有限生成中心での固有性、局所 Noether 基底での固有性を証明済み。
- 中心支持の補開集合を定義し、一般の blowup の中心外同型と構造射との交換式を構成済み。
- 一般の例外閉部分スキーム、中心への射、可換正方形、標準チャートの実際の商モデルと包含射を構成済み。
- 一般の例外閉部分スキームの有効 Cartier 性（正則な一元による局所商の条件）を証明済み。
- 冪比較の係数写像に対する自然性を証明し、一般の `blowupPowerIso : Bl(Iⁿ) ≅ Bl(I)` と基底上の交換式を構成済み。
- L7a の主要求（構成・例外因子・冪不変性・固有性・中心外同型）は一般スキーム上で実装済み。
- 工程区切りの全体ビルドは他レーン `InfinityCategories/F1/CoherentHomComparison.lean:167` の simp エラーで失敗。L7 の import 閉包と対象ビルドは正常。
- 次は blowup の普遍性と admissible 中心の共通細分、有限型平坦化の実際の中心の構成を進める。
- §14 の担当境界を採用済み（正本 §13-13、2026-10-18）。
- L7a・L7b と L7c の環論・古典的スキーム射を本レーンで完成させる。
- L7a の主要求は実装済み。層としての O(±1) の記号は導入しておらず、その符号照合は将来その記号を導入する際の補助項目。
- 例外イデアルの階数一自由化は各実チャート環の線形同型として構成済み。
- L7b は Noether 特殊形の主文を §7.1a に固定して着手済み。L7c の本体は未着手。
- 最初の admissible 中心と Cartier 化、位相的稠密性・スキーム論的稠密性を構成・証明済み。
- strict transform をスキーム論的像として構成し、固有性・Noether 性・U 上の同型を証明済み。
- 平坦・有限表示・分離な射を稠密な開部分上の同型から開埋め込みと判定する段階、および平坦な strict transform から実際の因子化射を作る段階を証明済み。
- 像中心が中心元の正則な像で生成される場合の実際のチャート環準同型・blowup への射と、基底上の一意性を証明済み。
- 任意の正則な単項像中心について、生成係数の基本開被覆を構成し、blowup への実際の大域持ち上げの存在と一意性を証明済み。
- 始域が任意のスキームでも、アフィン開被覆上で像中心が正則単項となる条件から普遍写像を構成し、その基底両立性と一意性を証明済み。
- 積中心 IJ の積生成元チャートの被覆性と因子中心の正則単項性を証明し、Bl_{IJ} から Bl_I・Bl_J への実際のアフィン比較射と基底交換式を構成済み。
- 積中心の比較射の自然性を証明して一般スキームへ大域化済み。積中心は admissible 性とアフィン局所有限生成性を保つ。
- 局所 Noether 基底上の有限個の admissible 中心の blowup を一つで共通支配する補題を証明済み。
- 同一基底上の有限中心の共通細分と、blowup 後の基底上にある中心の降下・合成の支配は区別する。次は後者のための幾何学的普遍性とイデアルの降下を進める。合成の支配はまだ未証明。
- 一般基底上でも、始域のアフィン被覆・基底アフィンへの係数写像・正則単項な像中心から、実際の普遍写像と基底上の存在一意性を証明済み。
- 正則単項中心のアフィン blowup の同型、およびアフィン開被覆上で正則単項な中心の一般 blowup の同型性を証明済み。
- 一チャート上の有限生成イデアルは、十分大きい任意の次数で I のその冪に含まれる基礎環イデアルへ降ろせる。
- 指定次数のチャート分数の演算と、全チャートのイデアル条件を満たす斉次な分子の候補中心を構成済み。各チャートで必要なイデアルへの包含と次数の増加は証明済み。
- 候補中心が十分大きい次数で全チャートの指定イデアルを生成する逆包含は未証明。次はチャートの重なりで分数とイデアルの局所化を比較する。
- 標準チャートの重なりを斉次局所化環の Spec と実際のファイバー積で同定し、両側の比による局所化と両射の交換式を証明済み。
- 重なりで同じ分子を持つ分数の比較式、整合するチャートイデアル族での比の冪による所属移送、有限個のチャートでの一様な分子補正を証明済み。
- Spec 上のイデアル層と環イデアルの順序同型を構成し、任意の環準同型の map・comap と両立することを証明済み。
- 実際の blowup 上のイデアル層から構成したチャートイデアル族の整合性を証明済み。Noether 基礎環ではチャート環も Noether で、各チャートイデアルは有限生成。
- 次は指定した有限チャート族に対する分子候補中心を用い、十分大きい次数で像イデアルが必要なイデアルに等しいことを証明する。全体の平坦化中心の存在はなお未証明。
- Noether でも実際に平坦な strict transform を達成する中心の存在と、admissible blowup の合成を一つで支配する段階は未証明。L7b 完了とはしない。
- 固定版 Mathlib に blowup の構成はない。
- 固定版 Mathlib には絶対 Proj とその構造射の固有性がある。
- Rees 代数は多項式環の部分代数として既にある。
- この部分代数に対する `GradedRing` は単項式射影から構成済み。
- 一般スキームでの blowup はアフィン構成の貼り合わせで与える。
- 相対 Proj を仮定する構造体は導入しない。
- L7b は下記の Noether スキームに限った主張を対象とする。
- L7c の K 群の同型そのものは本レーンの定理にしない。
- L7d の導来部分は K-L5 の構成と接続するまで未完了とする。

## 2. 目標

1. イデアルの blowup を実際のスキームとして構成する。
2. 構造射を定義して基底を明記する。
3. 中心の逆像を閉部分スキームとして定義する。
4. 逆像イデアルが可逆であることを証明する。
5. 例外閉部分スキームの有効 Cartier 性を証明する。
6. 正の冪に対する blowup の同型を証明する。
7. 有限生成中心に対する固有性を証明する。
8. 中心の補開集合上の同型を証明する。
9. 固有な modification を支配する blowup を構成する。
10. KST §5 の古典的な環論とスキーム論を証明する。
11. 既存の K 理論・導来幾何に依存させない。
12. 公開定理の全公理依存を標準三公理に限る。

## 3. 所有範囲

- Lean ソースは `SerrePositivity/KST/SchemeLemmas/`。
- namespace は `SerrePositivity.KST.SchemeLemmas`。
- 集約は `SerrePositivity/KST/SchemeLemmas.lean`。
- ルートには当該集約の `public import` 一行だけを加える。
- 公理監査は `scripts/audit_kst_scheme_lemmas.lean`。
- 本計画の変更は本レーンが行う。
- `CommutativeAlgebra/` は読み取り専用。
- 他レーンの計画・実装・監査を変更しない。
- KST 正本の変更も本レーンでは行わない。
- 導来 blowup は K-L5 の所有。
- pro 対象の一般論は K-L6 の所有。
- §10 の紙の検証の正本は K-L11 の所有。

## 4. 原典との対応

| 原典 | 内容 | 本レーンでの扱い |
| --- | --- | --- |
| KST §5.1、Prop 5.2 | 有限な抽象 blowup | 環論部分を証明 |
| KST §5.2、Claim 5.3 | 左逆元による帰着 | スキーム射の部分を証明 |
| KST §5.2、Prop 5.4 | 実際の blowup への帰着 | 支配射と左逆元の部分を証明 |
| KST §5.3、Lemma 5.5(i) | 導来構成と古典的構成の比較 | 古典的入力を証明 |
| KST §5.3、Lemma 5.5(ii)(iii) | 二重添字の消滅 | §10-9 の検証後に接続 |
| KST Lemma 5.6 | 有限射と blowup の塔 | 古典的有限射を本レーンで証明 |
| Stacks 081T | modification の blowup 支配 | Noether な特殊形から証明 |
| Stacks 01WQ Lemma 31.14.2 | 有効 Cartier 条件のアフィン局所モデル | 実際の商の Spec と包含射で定義・検証 |
| Temkin 2008 Lemma 2.1.5 | 同上の KST の引用元 | 番号を併記 |
| Huneke–Swanson Prop 8.1.5 | reduction と Rees 代数 | 原文の仮定を確認して証明 |
| Huneke–Swanson Thm 8.2.1 | 整依存と reduction | 有限射への適用を証明 |
| Artin–Rees | 冪と核の交わり | Mathlib の実証明を適用 |

KST は Kerz–Strunk–Tamme, *Algebraic K-theory and descent for blow-ups*。
基準の版は arXiv:1611.08466v4（2017-08-16）。
Stacks はタグを固定し、節番号変更による混同を避ける。
081T は取得時点で Lemma 38.31.4。
Temkin の対象は *Desingularization of quasi-excellent schemes in char 0*。
別の Temkin 論文の同番号と混同しない。
書籍の番号は Proposition と Theorem を区別する。
原文未確認の主張は確認済みと記さない。

## 5. 利用できる基盤

### 5.1 Mathlib の環論

- `reesAlgebra I` は `R[X]` の部分代数。
- 係数の条件は `f.coeff n ∈ I ^ n`。
- `reesAlgebra.monomial_mem` が単項式の所属を判定する。
- `reesAlgebra.as_sum_support` が有限和分解を与える。
- `adjoin_monomial_eq_reesAlgebra` が次数一生成性を与える。
- `reesAlgebra.fg` が有限生成性を与える。
- Noether 環上の有限型性は既存の instance。
- Rees 代数の Noether 性も既存の instance。
- `Ideal.exists_pow_inf_eq_pow_smul` が Artin–Rees を与える。
- 局所化と冪の写像の補題は既存 API を調べて適用する。
- Veronese の Proj 同型は独立した不足 API とする。

### 5.2 Mathlib のスキーム論

- `AlgebraicGeometry.Proj` が実際のスキームを返す。
- `Proj.toSpecZero` が零次成分の Spec への射を返す。
- `Proj.basicOpenIsoSpec` が斉次局所化のチャートを与える。
- `Proj.affineOpenCover` が Proj のアフィン開被覆を与える。
- 有限型な次数付き環の構造射は固有。
- `Proj.map` は次数を保つ準同型に対して定義済み。
- 冪の比較で必要な次数変更は通常の `Proj.map` と区別する。
- スキームの gluing は既存 API を使う。
- `Scheme.IdealSheafData` の局所表示 API を確認する。
- `IsClosedImmersion.of_comp` を切断に適用する。
- 等化子の閉埋め込みは `isClosedImmersion_equalizer_ι_left` を使う。
- 固有射の基底変換と合成に関する instance を使う。

### 5.3 リポジトリの環論

- `CommutativeAlgebra/ReesModule.lean` を読む。
- `CommutativeAlgebra/ReesModuleGrading.lean` を読む。
- Rees 加群の斉次成分の内部直和を参考にする。
- `CommutativeAlgebra/ArtinReesGrowth.lean` を読む。
- 正則列の既存宣言の仮定と依存を確認する。
- 必要な既存宣言は直接 import する。
- 未証明入力を含む大きな集約 import は避ける。
- 同じ定理を実装する前に利用可能性を確認する。

## 6. L7a：blowup

### 6.1 アフィン構成

1. `reesGrade I n` を Rees 代数内の次数 n 成分として定義する。
2. 係数条件による所属判定を証明する。
3. 零・加法・加法逆元について閉じることを証明する。
4. 次数 n、m の積が次数 n+m に属することを証明する。
5. 各 Rees 多項式の単項式分解を定義する。
6. 分解写像の加法性を証明する。
7. 分解と再構成が互いに逆であることを証明する。
8. `GradedRing` の instance を構成する。
9. 零次成分と基礎環の環同型を構成する。
10. `affineBlowup I := Proj (reesGrade I)` を定義する。
11. 零次成分の Spec 同型を通して構造射を定義する。
12. 基礎環の有限型性を零次成分上に移す。
13. 有限生成中心について構造射の固有性を証明する。
14. `I = ⊤` と `I = ⊥` の端点を検証する。

### 6.2 チャートと補開集合

1. a ∈ I に対する次数一単項式を定義する。
2. 標準開集合 D₊(at) の局所化環を記述する。
3. 分数 a/b の関係を斉次局所化で表す。
4. a が基礎環で可逆ならチャートが基底の D(a) と一致することを示す。
5. 標準開集合の重なりで環準同型の一致を示す。
6. D(I) 上の同型を貼り合わせる。
7. 同型と構造射の合成の等式を証明する。
8. 中心を避ける開集合への制限と両立することを示す。

### 6.3 例外閉部分スキーム

1. 中心 V(I) の逆像を閉部分スキームとして作る。
2. 逆像イデアルが各チャートで a に生成されることを示す。
3. チャート内の a が非零因子であることを示す。
4. 基礎環内での a の非零因子性は仮定しない。
5. 局所化の関係から Rees チャート上の性質を示す。
6. チャート間の生成元の比が単元であることを示す。
7. 可逆イデアルを貼り合わせる。
8. 有効 Cartier 因子としての例外因子を構成する。
9. O(1) = I O と符号規約を対応させる。
10. O(-1) = O(E) と記す場合の双対の向きを確認する。

### 6.4 冪と一般スキーム

1. n > 0 を明示する。
2. Rees(I^n) と Rees(I) の n 次 Veronese を比較する。
3. 環の同型と次数の再添字を区別する。
4. 斉次局所化の零次環の同型を作る。
5. 基本開集合上で Proj 同型を構成する。
6. 重なり上で同型が一致することを証明する。
7. 基礎スキーム上の同型であることを証明する。
8. アフィン局所化と blowup の可換性を証明する。
9. 一般のイデアル層に対して貼り合わせる。
10. アフィン被覆の選択への非依存を同型で表す。
11. 一般スキーム上の構造射を定義する。
12. 有限型な中心について固有性を局所化する。
13. 補開集合上の同型と例外因子を貼り合わせる。

## 7. L7b：平坦化による支配

### 7.1 最初に固定する文言

S を Noether スキーム、f : X → S を固有射とする。
U ⊆ S は開集合とする。
f の U への基底変換は同型と仮定する。
このとき S 上の有限型イデアル層 J と射 g : Bl_J(S) → X が存在する。
J の U への制限は単位イデアルである。
g ≫ f は blowup の構造射に等しい。
S の Noether 性は準コンパクト性を含む Mathlib の定義で扱う。
U の準コンパクト性は Noether 性から導く。
f の有限型性は固有性から導く。
これらを追加の未証明仮定として束ねない。
これは Stacks 081T / Temkin 2008 Lemma 2.1.5 の特殊形である。

### 7.1a 実装前に固定した Lean の主文（2026-10-18 再確認）

原典：https://stacks.math.columbia.edu/tag/081T （Lemma 38.31.4）。
証明の分解の参照：https://stacks.math.columbia.edu/tag/081S と tag/080Y。
既存の §7.1 の Noether 特殊形を維持する。主文は次の形とする。
これは計画上の文言であり、未証明の宣言を Lean ソースに追加しない。

```lean
theorem noetherian_blowup_domination
    {S X : Scheme} [AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (U : S.Opens) [IsIso (f ∣_ U)] :
    ∃ J : S.IdealSheafData,
      (∀ V : S.affineOpens, (J.ideal V).FG) ∧
      U ≤ centerComplement J ∧
      ∃ g : blowup J ⟶ X, g ≫ f = blowupπ J
```

U の準コンパクト性、S の準分離性、f の有限型性は既存の仮定から導く。
支配とは上記の実際の因子化を意味し、X 全体への全射性は追加しない。
最初の中心は U の閉補集合の消滅イデアル層から取る。
その blowup の例外因子の有効 Cartier 性は L7a の実証明を使う。
strict transform とその平坦化の有限型特殊形は未実装であり、仮定フィールドにしない。
最後の「固有な開部分スキームとスキーム論的稠密性から全体との一致」は独立に証明する。
二回の admissible blowup の合成を一回で表す段階も未証明のまま仮定しない。
この文言と方針をチャットへ報告した後、承認待ちを挟まず実装を進める。

### 7.2 証明の分解

1. 閉補集合を定義する有限型イデアル層を選ぶ。
2. 最初の admissible blowup で補集合を Cartier にする。
3. U のスキーム論的稠密性を導く。
4. strict transform を構成する。
5. 平坦化の必要な有限型特殊形を証明する。
6. strict transform を基底の開部分スキームにする。
7. strict transform の固有性を示す。
8. 開かつ閉な像と稠密性から全体との一致を示す。
9. 二回の blowup の合成を一つの admissible blowup で支配する。
10. 合成射の交換式を証明する。
11. 結論が実際の J と g の存在を返すことを確認する。
12. 平坦化定理を公理・型クラスのフィールドに移さない。

## 8. L7c：KST §5 の古典的部分

### 8.1 Prop 5.2

1. A → B の有限性と補開集合上の同型を正確に仮定する。
2. A のイデアル I と B 内での拡大を区別する。
3. 有限生成性により局所化での消滅指数を有限個選ぶ。
4. 鳩ノ巣原理で共通の冪 N を作る。
5. I^N B ⊆ image(A → B) を証明する。
6. 核の各生成元の消滅指数を求める。
7. 共通冪で核を消す。
8. Artin–Rees を核部分加群に適用する。
9. 十分大きい N に対し I^N ∩ ker(A → B) = 0 を示す。
10. 大きい指数への単調性を別に証明する。
11. K 固有の Cor 4.12 は本ファイルから import しない。

### 8.2 Claim 5.3・Prop 5.4

1. 固有射の切断が閉埋め込みになることを証明する。
2. α と β の始域・終域を明記する。
3. 左逆元の等式をスキーム射の等式として記す。
4. 等化子の閉埋め込みを用いて比較射の像を扱う。
5. 一般の K 群への適用は利用側に残す。
6. 抽象的な retract の命題と幾何的な構成を区別する。

### 8.3 Huneke–Swanson と Lemma 5.6 の古典的入力

1. a′(2) は生成元ごとの二乗のイデアルとして定義する。
2. (a′)^2 はイデアルの二乗として定義する。
3. 二つのイデアルを定義上同一視しない。
4. 交差項の整依存のモニック方程式を作る。
5. Rees 代数の拡大の整性を証明する。
6. 有限型性と整性から有限性を証明する。
7. Proj 上の有限射をチャート上で構成する。
8. Bl_{(a′)^2} ≅ Bl_{a′} と合成する。
9. 導来塔との接続は L7d に残す。

### 8.4 Lemma 5.5

1. (i) の古典的な比較射を構成する。
2. 導来零次ホモトピーとの比較自体は K-L5 に接続する。
3. (ii)(iii) の m と厚み指数 n の順序を固定する。
4. m に依存する指数を一様と呼ばない。
5. §10-9 の紙の確認を実装の前に行う。
6. K-L6 の対角共終性の宣言に接続する。

## 9. §10-9：実装前の紙の確認

対象は Lemma 5.5(ii)(iii) の二重添字と Isaksen 4.7 の置換。
現状は未着手であり、検証済みとはしない。
実装前に原文の量化子をこの節に記す。
固定した m の後に n を選ぶ主張と、一様 n の主張を分ける。
対角に必要な単調な上界の存在を確認する。
有限個の前段への条件を最大値でまとめる方針を検討する。
導来次数に関する一様性も別に確認する。
主張と証明方針を記録してチャットに報告してから実装する。
報告後に承認待ちを挟まない。
未解決の設計変更が必要な場合は提案として停止する。

## 10. L7d：合流条件

- K-L5 の導来 blowup の実在する定義を受け取る。
- 古典的 truncation との比較の型を合わせる。
- X̃(2^n) の遷移射と合成則を確認する。
- Lemma 5.6 の有限射を当該遷移射と比較する。
- Thm A の K 群側の組み立ては利用側と合流する。
- L7d が未完了の間は古典的部分だけの完了を報告する。

## 11. 主要宣言の表

以下は予定名であり、実装済みでないものを `#check` 済みとは扱わない。

| 宣言 | ファイル | 状態 | 役割 |
| --- | --- | --- | --- |
| `reesProjection` | Blowup | 検証済み | 単項式射影 |
| `reesGrade` | Blowup | 検証済み | Rees の斉次成分 |
| `mem_reesGrade_iff` | Blowup | 検証済み | 斉次所属の判定 |
| `isInternal_reesGrade` | Blowup | 検証済み | 内部直和 |
| `reesGradeGradedRing` | Blowup | 検証済み | Proj の入力 |
| `reesZeroEquiv` | Blowup | 検証済み | 零次成分と R |
| `affineBlowup` | Blowup | 検証済み | アフィン blowup |
| `affineBlowupπ` | Blowup | 検証済み | 構造射 |
| `rees_finiteType_over_zero` | Blowup | 検証済み | 零次成分上の有限型性 |
| `affineBlowupπ_isProper` | Blowup | 検証済み | 有限生成中心での固有性 |
| `affineCenterι` | Blowup | 検証済み | 中心の閉埋め込み |
| `affineExceptional` | Blowup | 検証済み | 中心のスキーム論的逆像 |
| `affineExceptionalι_isClosedImmersion` | Blowup | 検証済み | 例外閉部分スキームの閉性 |
| `affineExceptional_square` | Blowup | 検証済み | blowup 正方形の交換式 |
| `reesMonomial` / `reesDegreeOne` | Blowup | 検証済み | 斉次生成元 |
| `affineBlowupChartIso` | Blowup | 検証済み | 標準チャートの Spec 同型 |
| `rees_adjoin_zero_degreeOne` | Blowup | 検証済み | 零次成分上の次数一生成性 |
| `iSup_affineBlowupChart` | Blowup | 検証済み | 標準チャートの被覆性 |
| `chartBaseMap` / `chartRatio` | ChartAlgebra | 検証済み | チャートの係数写像と生成元の比 |
| `affineBlowupChartIso_inv_ι_π` | ChartAlgebra | 検証済み | 実際のスキーム構造射との一致 |
| `chartBaseMap_mul_ratio` | ChartAlgebra | 検証済み | a · (b/a) = b |
| `chart_map_ideal_eq_span` | ChartAlgebra | 検証済み | 中心の拡大イデアルの単項生成 |
| `chartBaseMap_mem_nonZeroDivisors` | ChartAlgebra | 検証済み | チャートでの生成元の非零因子性 |
| `chart_clear_denominator` | ChartLocalization | 検証済み | a の冪による分母消去 |
| `chartBaseMap_eq_iff` | ChartLocalization | 検証済み | a の冪による係数の等式判定 |
| `chart_localization_isLocalizationMap` | ChartLocalization | 検証済み | チャート局所化の普遍条件 |
| `chartAwayEquiv` | ChartLocalization | 検証済み | R[1/a] とチャートの a 局所化の同型 |
| `chartAwayEquiv_apply_base` | ChartLocalization | 検証済み | 基礎環の係数保存 |
| `proj_basicOpenToSpec_forget` | ProjBase | 検証済み | Proj のスキーム実装と局所環付き空間の実装の比較 |
| `proj_basicOpenToSpec_mk_mem` | ProjBase | 検証済み | 斉次分数の素イデアルへの所属 |
| `proj_toSpecZero_mem` | ProjBase | 検証済み | 構造射での素イデアルの交わり |
| `proj_toSpecZero_preimage_basicOpen` | ProjBase | 検証済み | 零次基本開集合の逆像 |
| `affineBlowupπ_preimage_basicOpen` | BlowupAway | 検証済み | 基礎環の基本開集合の逆像 |
| `affineBlowupπ_preimage_basicOpen_le_chart` | BlowupAway | 検証済み | 逆像が一つの標準チャートに入る |
| `affineBlowupπ_restrict_basicOpen_isIso` | BlowupAway | 検証済み | D(a) 上の構造射の同型性 |
| `affineCenterComplement` / `mem_affineCenterComplement` | BlowupAway | 検証済み | D(I) = Spec R ∖ V(I) |
| `affineBlowupπ_restrict_complement_isIso` | BlowupAway | 検証済み | 中心の補集合上の同型性 |
| `affineBlowupAwayIso` / `affineBlowupAwayIso_hom_ι` | BlowupAway | 検証済み | 実際の基底上のスキーム同型 |
| `specQuotientPullbackIso` / `specQuotientPullbackIso_inv_fst` | QuotientPullback | 検証済み | 商の Spec の逆像とその包含 |
| `affineExceptionalChartIso` / `affineExceptionalChartIso_inv_snd` | Exceptional | 検証済み | 例外閉部分スキームの実際のチャート同型 |
| `IsEffectiveCartierImmersion` | Cartier | 実装済み | 閉埋め込みの局所正則方程式による定義 |
| `affineExceptional_isEffectiveCartier` | Cartier | 検証済み | アフィン例外因子の有効 Cartier 性 |
| `regularPrincipalIdealEquiv` / `chartExceptionalIdealEquiv` | Cartier | 検証済み | 正則単項イデアル・例外イデアルの局所自由化 |
| `chart_clear_denominator_mem` | ChartLocalization | 検証済み | I^m に属する分子を保つ分母消去 |
| `chartToBaseLocalization` / `chartToBaseLocalization_injective` | ChartEmbedding | 検証済み | 標準チャートの R[1/a] への単射 |
| `mem_chartToBaseLocalization_range_iff` | ChartEmbedding | 検証済み | 分子 I^m、分母 a^m による像の判定 |
| `awayPowEquiv` | PowerCharts | 検証済み | R[1/a^n] と R[1/a] の基底上の同型 |
| `powerChart_range_eq` | PowerCharts | 検証済み | 対応する冪チャートの共通局所化内の像の一致 |
| `powerChartEquiv` / `powerChartEquiv_base` | PowerCharts | 検証済み | 対応する冪チャート環の係数を保つ同型 |
| `prime_contains_degreeOne_of_contains_powers` | PowerChartCover | 検証済み | 純冪から積生成元への素イデアル判定 |
| `iSup_affineBlowup_powerCharts` | PowerChartCover | 検証済み | 純冪チャートによる冪中心の blowup の被覆 |
| `specMap_ker_eq_bot_of_injective` | SeparatedExt | 検証済み | 単射な環準同型の Spec の零核 |
| `hom_ext_of_ker_eq_bot_of_separated` | SeparatedExt | 検証済み | 非被約スキームでも使える比較射の一意性 |
| `pullback_snd_ker_eq_bot_of_openImmersion` | SeparatedExt | 検証済み | 開基底変換での零核の保存 |
| `hom_ext_of_isIso_restrict` | SeparatedExt | 検証済み | 補開集合上の比較の一意性 |
| `affineBlowupChartCover` | ChartGluing | 検証済み | 次数一元による実際のアフィン開被覆 |
| `affineBlowupπ_isSeparated` | ChartGluing | 検証済み | 有限生成性なしの分離性 |
| `chartLocalizationι_ker_eq_bot` | ChartGluing | 検証済み | 非零因子局所化による零核の検出 |
| `chart_overlap_hom_ext` | ChartGluing | 検証済み | 重なり上の基底上の射の一致 |
| `affineBlowup_hom_ext` | ChartGluing | 検証済み | 中心外で同型な分離標的への射の一意性 |
| `affineBlowupPowerChartCover` | PowerBlowup | 検証済み | 純冪チャートによる実際のアフィン開被覆 |
| `powerBlowupMap` / `powerBlowupInv` | PowerBlowup | 検証済み | 正の冪との両方向の基底上の比較射 |
| `affineBlowupPowerIso` | PowerBlowup | 検証済み | 任意の可換環での正の冪の blowup 同型 |
| `affineBlowupPowerIso_hom_base` | PowerBlowup | 検証済み | 冪不変性の同型と構造射の両立 |
| `reesMap` / `reesGradedMap` | ReesMap | 検証済み | 中心を保つ係数環準同型の次数付き Rees 写像 |
| `reesMap_surjective` / `reesMap_injective` | ReesMap | 検証済み | 係数環の全射性・単射性の保存 |
| `reesGradedMap_irrelevant_le` | ReesMap | 検証済み | 像中心についての irrelevant ideal の包含 |
| `proj_map_toSpecZero` | ProjMap | 検証済み | 一般の Proj の構造射の自然性 |
| `affineBlowupBaseMap` / `affineBlowupBaseMap_base` | BaseChangeMap | 検証済み | 任意の環準同型に対する基底上の比較射 |
| `rees_localization_clear_denominator` | ReesLocalization | 検証済み | 各中心冪の所属を保つ共通分母の消去 |
| `reesMap_isLocalizationMap` | ReesLocalization | 検証済み | Rees 係数写像の局所化の普遍条件 |
| `reesLocalizationEquiv` / `reesLocalizationEquiv_base` | ReesLocalization | 検証済み | 定数分母による Rees 局所化の環同型と係数保存 |
| `rees_localization_clear_homogeneous` | ReesLocalization | 検証済み | 同次数の斉次元での分母消去 |
| `chartBaseChangeMap` / `chartBaseChangeMap_base` | ChartBaseChange | 検証済み | 標準チャートの係数写像と係数保存 |
| `chartBaseChangeMap_mk` | ChartBaseChange | 検証済み | 斉次分数に対する比較写像の計算 |
| `chart_localization_clear_denominator` | ChartBaseChange | 検証済み | 局所化後のチャートの共通分母消去 |
| `localization_awayMap_isLocalizationMap` | LocalizationCommute | 検証済み | 係数分母と一元局所化の交換 |
| `chartBaseChangeMap_val` | ChartBaseChange | 検証済み | 通常の Rees 局所化の写像との両立 |
| `chartBaseChangeMap_isLocalizationMap` | ChartBaseChange | 検証済み | チャート比較写像の局所化の普遍条件 |
| `chartCoefficientLocalizationEquiv` | ChartBaseChange | 検証済み | 係数局所化後のチャートの環同型 |
| `iSup_affineBlowup_imageCharts` / `affineBlowupImageChartCover` | BaseChangeChartCover | 検証済み | 元の中心元の像によるチャート被覆 |
| `proj_awayι_map_of_eq` | ProjMap | 検証済み | 分母の等式を移送した Proj の局所比較公式 |
| `affineBlowupBaseMap_chart` / `affineBlowupBaseMap_preimage_chart` | BaseChangeCharts | 検証済み | チャート射の交換式と逆像の同定 |
| `affineBlowupBaseMap_isOpenImmersion` / `affineBlowupBaseMap_range` | BlowupLocalization | 検証済み | 一元係数局所化の比較射の開埋め込み性と像 |
| `affineBlowupLocalizationIso` / `affineBlowupLocalizationIso_hom_ι` | BlowupLocalization | 検証済み | D(r) の逆像との基底上のスキーム同型 |
| `reesGradedMap_id` / `reesGradedMap_comp` | ReesMap | 検証済み | 次数付き係数写像の恒等性と合成則 |
| `affineBlowupCenterMap` | BlowupFunctor | 検証済み | 中心の像を同定した基底上の比較射 |
| `affineBlowupCenterMap_id` / `affineBlowupCenterMap_comp` | BlowupFunctor | 検証済み | 中心比較射の恒等性と反変合成則 |
| `affineBlowupRingEquivIso` / `affineBlowupRingEquivIso_hom_base` | BlowupRingEquiv | 検証済み | 基礎環同型による blowup の移送と基底両立性 |
| `affineBlowupModel` / `affineBlowupModelMap` | AffineModels | 検証済み | イデアル層のアフィン局所モデルと包含に沿う比較 |
| `affineBlowupDiagram` | AffineModels | 検証済み | 局所モデルとその比較の実際の関手 |
| `affineBlowupModelToBase` / `affineBlowupModelMap_toBase` | AffineModels | 検証済み | 局所モデルの基底上の構造射と自然性 |
| `affineBlowupModelMap_basicOpen_range` | AffineModelLocalization | 検証済み | 基本開集合への局所比較の像 |
| `affineBlowupModelMap_common_basic` | AffineModelOpenImmersion | 検証済み | 二つのアフィン開で基本開となる共通モデル |
| `affineBlowupModelMap_injective` / `affineBlowupModelMap_isOpenImmersion` | AffineModelOpenImmersion | 検証済み | 任意のアフィン開包含の比較の単射性と開埋め込み性 |
| `affineBlowupModelMap_range` / `affineBlowupModelMap_opensRange` | AffineModelRange | 検証済み | 任意のアフィン開包含に沿う比較の像 |
| `affineBlowupDiagram_isLocallyDirected` | SchemeBlowup | 検証済み | 局所モデルの図式の局所的有向性 |
| `blowup` / `blowupπ` | SchemeBlowup | 検証済み | 全アフィン局所モデルの開貼り合わせによる通常の blowup と構造射 |
| `blowupAffineι` / `blowupOpenCover` | SchemeBlowup | 検証済み | アフィン局所モデルからの標準開包含と被覆 |
| `blowupAffineIso` / `blowupAffineIso_hom_restrict` | SchemeBlowupAffine | 検証済み | アフィン上の Rees Proj との同型と構造射の両立 |
| `blowupπ_isSeparated` / `blowupπ_isProper` | SchemeBlowupProper | 検証済み | 一般の分離性と局所有限生成中心での固有性 |
| `blowupπ_isProper_of_isLocallyNoetherian` | SchemeBlowupProper | 検証済み | 局所 Noether 基底での固有性 |
| `centerComplement` / `fromSpec_preimage_centerComplement` | SchemeBlowupAway | 検証済み | 中心補集合とアフィン切断中心の補集合との比較 |
| `blowupπ_restrict_complement_isIso` | SchemeBlowupAway | 検証済み | 一般の blowup の中心外同型性 |
| `blowupAwayIso` / `blowupAwayIso_hom_ι` | SchemeBlowupAway | 検証済み | 中心外の実際のスキーム同型と構造射の交換式 |
| `subschemeAffinePullbackIso` / `subschemeChartPullbackIso` | SubschemeAffinePullback | 検証済み | 中心の逆像の実際の商の Spec のモデルと射影保存 |
| `exceptional` / `exceptionalι` / `exceptionalToCenter` / `exceptional_square` | SchemeExceptional | 検証済み | 一般の例外閉部分スキームと古典的 blowup 正方形 |
| `exceptionalChartIso` / `exceptionalChartIso_inv_snd` | SchemeExceptional | 検証済み | 例外因子の標準チャートの商モデルと包含射 |
| `exceptional_isEffectiveCartier` | SchemeExceptional | 検証済み | 一般の例外因子の正則な局所方程式 |
| `affineBlowupCenter_hom_ext` | BaseComparisonExt | 検証済み | 係数環を変えた中心比較射の一意性 |
| `affineBlowupPowerIso_naturality` | PowerNaturality | 検証済み | 任意の係数環写像に対する冪比較の自然性 |
| `affineBlowupPowerNatIso` | SchemePowerBlowup | 検証済み | アフィン局所モデル図式の冪比較自然同型 |
| `blowupPowerIso` / `blowupPowerIso_hom_base` | SchemePowerBlowup | 検証済み | 一般スキーム上の正の冪不変性と基底両立性 |
| `IsUAdmissibleCenter` / `blowupπ_restrict_admissible_isIso` | Flattening | 検証済み | U を避ける中心と U 上の同型 |
| `initialAdmissibleCenter` / `exists_initial_admissible_blowup` | Flattening | 検証済み | 閉補集合の消滅イデアルによる最初の固有な Cartier 化 |
| `strictTransform` / `strictTransformπ` / `strictTransformToOriginal` | StrictTransform | 検証済み | 開部分のスキーム論的像による実際の対象と射 |
| `strictTransformπ_isProper` / `strictTransform_isNoetherian` | StrictTransform | 検証済み | 固有性と Noether 性の移送 |
| `strictTransformπ_restrict_isIso` | StrictTransform | 検証済み | U 上の同型の保持 |
| `blowup_centerComplement_dense` | BlowupDensity | 検証済み | 中心外開集合の位相的稠密性 |
| `blowup_centerComplement_isSchemeTheoreticallyDominant` | BlowupSchemeDensity | 検証済み | Noether 基底での中心外開包含の零核 |
| `isIso_of_proper_openImmersion_dense_restrict` | ProperOpenIso | 検証済み | 固有な開埋め込みの最後の同型判定 |
| `isOpenImmersion_of_flat_iso_on_dense_open` | FlatOpenImmersion | 検証済み | 平坦・有限表示・分離から開埋め込みへの判定 |
| `exists_domination_of_flat_schematicallyDense_strictTransform` | FlatStrictTransform | 検証済み | 平坦化済みの strict transform から実際の因子化の構成 |
| `chartRegularLift` / `chartRegularLift_base` | ChartRegularLift | 検証済み | 正則な単項像中心からの環準同型 |
| `chart_hom_ext_of_regular` | ChartRegularLift | 検証済み | 分母消去による環準同型の一意性 |
| `affineBlowupRegularLift` / `affineBlowupRegularLift_base` | AffineRegularLift | 検証済み | 基底上の実際の局所普遍写像 |
| `affineBlowup_hom_ext_of_regular` | AffineRegularLift | 検証済み | 正則局所化と分離性による射の一意性 |
| `span_regularCenterCoefficients` / `iSup_regularCenterCoefficient_basicOpen` | RegularCenterCover | 検証済み | 任意の正則単項生成元を中心元の像へ局所化 |
| `regularCenter_localized_regular` / `regularCenter_localized_image` | RegularCenterCover | 検証済み | 局所的な普遍写像の条件 |
| `local_lift_overlap_hom_ext` | LocalLiftGluing | 検証済み | 零核の検出射による重なり上の一意性 |
| `affineBlowupPrincipalRegularLift` / `existsUnique_affineBlowup_lift_of_principal_regular` | PrincipalRegularLift | 検証済み | 任意の正則単項像中心からの存在と一意性 |
| `principalDetector_range_complement` | PrincipalDetector | 検証済み | 単項生成元の局所化の像は中心外 |
| `affineBlowupCoverLift` / `existsUnique_affineBlowup_cover_lift` | AffineUniversal | 検証済み | 任意の始域と局所正則単項条件による普遍写像 |
| `ideal_eq_span_of_regular_product` / `productChart_left_image` | ProductCenter | 検証済み | 積中心チャートで因子中心を単項化 |
| `affineBlowupProductChartCover` | ProductChartCover | 検証済み | 積生成元による実際のアフィン開被覆 |
| `affineBlowupProductLeftMap` / `affineBlowupProductRightMap` | ProductBlowup | 検証済み | 二つのアフィン blowup の共通細分の比較射 |
| `affineBlowupProductLeftMap_naturality` | ProductNaturality | 検証済み | 積中心の比較射の係数写像に対する自然性 |
| `blowupProductLeftMap` / `blowupProductRightMap` | SchemeProductBlowup | 検証済み | 一般スキーム上の二つの中心の共通細分 |
| `centerComplement_mul` / `isUAdmissibleCenter_mul` | AdmissibleRefinement | 検証済み | 積中心の中心外開集合と admissible 性 |
| `productCenter_finiteGeneration` | AdmissibleRefinement | 検証済み | 積中心のアフィン局所有限生成性 |
| `exists_admissible_binary_refinement` / `exists_admissible_finite_refinement` | AdmissibleRefinement | 検証済み | 同一基底上の二中心・有限個の中心の共通支配 |
| `affineBlowupPrincipalIso` / `affineBlowupπ_isIso_of_regular_principal` | PrincipalBlowupIso | 検証済み | 正則単項中心の blowup の自明性 |
| `blowupπ_isIso_of_locally_regular_principal` | LocallyPrincipalBlowup | 検証済み | 局所的に可逆な中心の一般 blowup の自明性 |
| `blowupUniversalLift` / `existsUnique_blowup_universal_lift` | BlowupUniversal | 検証済み | 一般基底・始域上の実際の普遍写像と存在一意性 |
| `chart_finite_clear_denominators` | ChartIdealDescent | 検証済み | 有限個のチャート切断の同時分母消去 |
| `chart_finite_ideal_descent` / `chart_finite_ideal_descent_eventually` | ChartIdealDescent | 検証済み | 一チャート上の有限生成イデアルの各十分大次数での降下 |
| `chartFraction` / `chartFraction_clear` / `chartFraction_mul` | ChartFractions | 検証済み | 指定次数の斉次分数とその演算 |
| `homogeneousNumeratorIdeal` / `homogeneousNumeratorIdeal_map_le` / `homogeneousNumeratorIdeal_mul_le` | HomogeneousNumerators | 検証済み | 全チャートの条件を満たす実際の分子候補中心と包含・次数増加 |
| `affineBlowupChartOverlapIso` / `chartOverlap_isLocalizationLeft` / `chartOverlap_isLocalizationRight` | ChartOverlap | 検証済み | 重なりの実際の環モデルと両側の局所化 |
| `chartOverlap_fraction` / `chartOverlap_left_ratio_isUnit` | ChartOverlapFractions | 検証済み | 重なり上の斉次分数の比較と比の可逆性 |
| `ChartIdealsCompatible` / `chart_fraction_mem_after_numerator_pow` | CompatibleChartIdeals | 検証済み | 像イデアルの整合性と分子補正による所属移送 |
| `specIdealEquiv` / `specIdealEquiv_map` / `specIdealEquiv_comap` | SpecIdeal | 検証済み | アフィンのイデアル層と環イデアルの対応・関手性 |
| `blowupChartIdeal` / `blowupChartIdeals_compatible` / `blowupChartIdeal_fg` | BlowupChartIdeals | 検証済み | 実際のイデアル層からの整合族と Noether 時の有限生成性 |
| `chart_fraction_mem_on_finite_charts` | FiniteChartNumerators | 検証済み | 指定した有限チャート族での分子補正の一様化 |
| `exists_admissibleBlowup_dominating` | Flattening | 予定 | 081T の特殊形 |
| Prop 5.2 の環論 | Section5 | 予定 | 冪・像・核 |
| Claim 5.3 の左逆元 | K-L6 | 担当外 | K/pro の結論 |
| Prop 5.4 の支配 | K-L6 | 担当外 | 実 blowup への帰着の K/pro 部分 |
| Huneke–Swanson の有限射 | Section5 | 予定 | 二乗生成元の比較 |
| Lemma 5.5 の古典的入力 | Section5 | 予定 | 導来比較への入力 |

## 12. 保存・検証・コミット

1. 保存単位の対象モジュールを `lake build` する。
2. `set -o pipefail` を設定して終了コードを確認する。
3. 監査は集約 import の公開宣言と補助生成宣言を調べる。
4. 監査は `Lean.collectAxioms` で依存公理を再帰的に収集する。
5. 許可する公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
6. `sorryAx` もその他の独自公理も拒否する。
7. 宣言数ゼロの監査は成功扱いにしない。
8. `git diff --check` を確認する。
9. コミット対象は自分の検証済みファイルに限る。
10. `git commit --only` を使う。
11. ルートの他レーンの差分を取り込まない。
12. amend・rebase・reset は使わない。
13. 工程の区切りで全体ビルドを行う。
14. 並行作業による自分の import 閉包の破損では回避策を作らず報告する。
15. 工程の完了時に現在地と主要宣言の表を書き換える。

## 13. 設計上の決定

- 論文の番号を Lean のモジュール説明と宣言の説明に記す。
- docstring は概要／方針／規約／使われ方を日本語で書く。
- 実際の数学的構造の法則だけを構造体に持たせる。
- 未証明の平坦化・有限性・同型を構造体の仮定に押し込まない。
- 名前だけの定理や自明な条件付き言い換えで工程完了としない。
- 環は原則 `CommRing`、スキームは Mathlib の `Scheme` を使う。
- blowup の一般構成を K の界面から独立させる。
- 有限生成性が必要な箇所だけに仮定を置く。
- Noether 特殊形から始めても一般化の余地を型に残す。
- 正の冪の比較では n = 0 を含めない。
- 例外因子は逆像閉部分スキームと Cartier 構造を区別する。
- Rees 代数の指数と多項式次数の一致を明示する。
- 状態が変わった節は追記の履歴でなく現状に書き換える。

## 14. 担当境界（採用済み、正本 §13-13）

原典確認先：KST arXiv:1611.08466v4 §5.3、Table 1、Lemma 5.5 とその証明。
URL：<https://arxiv.org/html/1611.08466v4>。
L7c の全体を「古典的スキーム論で K に依存しない」まま実装することは、
Lemma 5.5 の原文の型とは両立しない。
これは Lean の基盤不足ではなく、結論自体が K 理論についての主張であるため。

### 14.1 原文の主張と依存

| 項目 | 原文の結論 | 原文の主な依存 |
| --- | --- | --- |
| Lemma 5.5(i) | Koszul 導来閉部分スキームから通常の商への K 理論の pro 同値 | Prop 4.8、Lemma 4.10 |
| Lemma 5.5(ii) | 導来 blowup とその厚みの相対 K から underlying scheme の相対 K への pro 同値 | Čech 降下、Cor 4.13 |
| Lemma 5.5(iii) | derived exceptional と semi-derived exceptional の K 理論の pro 同値 | Lemma 4.1、4.10、Prop 4.8、Čech 降下 |
| Claim 5.3 | K 理論 pro 正方形の homotopy cartesian 性 | Prop 5.2、Lemma 4.7、blowup 降下の仮定 |
| Prop 5.4 | 実 blowup の降下から Thm A への帰着 | Claim 5.3、pro 群の左逆元論法 |

これらの原文の本体は K の界面と pro の型を必要とする。
本レーンで幾何学的入力を証明することと、本体を証明したことを混同しない。

### 14.2 二種類の古典的スキームを区別する

- `Bl_(a)(Spec A)` は本レーンの Rees 代数の Proj。
- KST §5.3 の `X̃` は導来 blowup の underlying scheme。
- 原文は Remark 3.3 による前者から後者への閉埋め込みを使う。
- その射は中心の外では同型だが、一般には大域同型ではない。
- したがって `X̃ := affineBlowup I` という定義で接続してはならない。
- K-L5 から underlying scheme の定義を受け取り、別の対象として比較する。
- 正則な普遍基底上の通常 blowup と、任意の基底変更後の通常 blowupも区別する。

### 14.3 採用した分担

1. L7 は現在の禁止事項どおり K 非依存を保つ。
2. L7a・L7b、および L7c の環論・古典的スキーム射を L7 で完成させる。
3. Lemma 5.5 と Claim 5.3・Prop 5.4 の K/pro の結論は K-L6 が Thm 4.11・Cor 4.12・4.13 の後に担当する。
4. L7 は K-L5 の対象を仮定し、underlying scheme との比較に必要な閉埋め込みと中心の外での同型を用意する。
5. pro の再添字と対角共終性は K-L6 の宣言を使う。
6. Prop 5.2 の鳩ノ巣と Artin–Rees、Huneke–Swanson 8.1.5・8.2.1、冪の blowup 同型と Lemma 5.6 の古典的部分は L7 が完成させる。

この分担により、独立性と原典の宣言の型を両立する。
未証明本体を公理や構造体フィールドとして L7 に取り込む案は採らない。

### 14.4 §10-9 の量化子と証明方針（実装前記録）

Lemma 5.5(ii)(iii) 自体は一つの blowup と厚み指数 n の pro 系について述べる。
Lemma 5.6 の証明で blowup の指数 m を追加し、各固定 m に Lemma 5.5 を適用する。
その後、二重添字の pro 系から対角 n = m への移行が必要になる。
各段階で遷移写像が可換することを先に用意し、有限個の既指定段階の上界を取る。
全 m に共通の厚み指数が存在するという主張を、固定 m の結論から推論しない。
π_i の消滅・同型に必要な指数の i への依存も別に扱う。
この再構成が原文の Lemma 4.7 の利用を完全に置換できるかは未検証。
この K/pro の再構成と Lean 実装は K-L6 の担当とし、L7 は古典的幾何の入力を提供する。
本節の記録と設計上の問題はチャットに報告済み。

### 14.5 L7a の現在地と補助項目

- 一般の例外因子の正則な局所商モデルを証明済み。各チャートの拡大イデアルの線形自明化を使う。
- 中心の補開集合上の同型は一般スキーム上でも構成済み。アフィン局所モデルとの比較を介して証明した。
- 正の冪の比較は一般のイデアル層について自然同型と余極限で大域化済み。
- 一元局所化との比較、全アフィン開集合の図式、一般スキームへの開貼り合わせは構成済み。
- L7a 区切りの対象ビルドと公理監査（500 宣言）は成功。全体ビルドは他レーンの CoherentHomComparison:167 で失敗し報告済み。
- 共有ルートに追加した一行の import は、他レーンの差分から分離できるまで未コミット。
